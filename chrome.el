;;; chrome.el --- Google Chrome remote tab control -*- lexical-binding: t; -*-

;; Copyright (C) 2020 xristos@sdf.org
;;               2020 bas@anti.computer
;;
;; All rights reserved

;; Modified: 2020-05-18
;; Version: 0.5
;; Author: xristos <xristos@sdf.org>
;;      Bas Alberts <bas@anti.computer>
;;
;; Maintainer: Bas Alberts <bas@anti.computer>
;; URL: https://github.com/anticomputer/chrome.el
;; Package-Requires: ((emacs "25.1"))
;; Keywords: comm

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;;
;;   * Redistributions of source code must retain the above copyright
;;     notice, this list of conditions and the following disclaimer.
;;
;;   * Redistributions in binary form must reproduce the above
;;     copyright notice, this list of conditions and the following
;;     disclaimer in the documentation and/or other materials
;;     provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;; ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
;; LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;; CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;; SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;; CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;; ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;; POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:
;;
;; Remotely manage tabs belonging to one or more Chrome processes.
;;
;; Communication takes place over Chrome DevTools protocol
;;
;;; Usage:
;;
;; M-x chrome
;;
;; Please see README.org for documentation.

;;; Code:

(require 'url)
(require 'json)
(require 'subr-x)
(require 'cl-lib)
(require 'auth-source)

(defgroup chrome nil
  "Google Chrome remote tab control."
  :group 'comm)

(defface chrome-tab-filter-face
  '((((class color) (background dark))  (:foreground "#aaffaa"))
    (((class color) (background light)) (:foreground "#5faf00")))
  "Face used to display current filter."
  :group 'chrome)

(defface chrome-tab-active-face
  '((((class color) (background dark))  (:foreground "#aaffaa"))
    (((class color) (background light)) (:foreground "#5faf00")))
  "Face used to display tabs that are active in the browser."
  :group 'chrome)

(defface chrome-tab-marked-face
  '((((class color) (background dark))  (:foreground "#ffaaff"))
    (((class color) (background light)) (:foreground "#d70008")))
  ""
  :group 'chrome)

(defface chrome-tab-deleted-face
  '((((class color) (background dark))  (:foreground "#8d021f"))
    (((class color) (background light)) (:foreground "#8d021f")))
  ""
  :group 'chrome)

(defface chrome-tab-marked-active-face
  '((((class color) (background dark))  (:foreground "#ffffaa"))
    (((class color) (background light)) (:foreground "#800080")))
  ""
  :group 'chrome)

(defvar chrome-render-function #'chrome-render-tab
  "Function that renders a tab into a string for display.

The function must accept one argument, an chrome-tab instance,
and return a string that must not span more than one line.")

(defvar chrome-limit-function #'chrome-limit-tab
  "Function that limits visible tabs based on certain criteria.

Function must accept one argument, an chrome-tab instance, and
return t if the tab is included in the limit, nil otherwise.")

(defvar chrome-filter-function #'chrome-filter-tab
  "Function that filters visible tabs based on a user-typed regexp.

Function must accept one argument, chrome-tab instance, and
return t if the tab passes the filter, nil otherwise. The current
filter can be retrieved by calling `chrome-active-filter'.")

(defvar chrome-show-timing t
  "Measure and display elapsed time after every operation.

This can be toggled by `chrome-toggle-timing'.")

(defvar chrome-default-view :title
  "Show tab titles when equal to :title, URLs otherwise.
This can be toggled by `chrome-toggle-url-view'.")

(defvar chrome-default-limit :all
  "Default limit.

Can be one of :all, :mark, :dup, :active or a pair specifying a (PORT . HOST).
This can be toggled by:

 `chrome-limit-none'
 `chrome-limit-marked'
 `chrome-limit-dup'
 `chrome-limit-active'
 `chrome-limit-session'.")

(defvar chrome-sessions (list (cons 9222 "127.0.0.1"))
  "A list of DevTools sessions which are pairs of (port . host).

You can enable a DevTools remote debugging port for Chrome with:

--remote-debugging-port=9222

Note that anyone who can send direct, or indirect, requests to this
port can drive, inspect, and otherwise influence your Chrome session.")

(defvar chrome-auto-retrieve nil
  "If non-nil, retrieve all tabs after certain operations.

Note that every retrieval recreates tab state in Emacs and thus discards
what was previously there (except filter and limit).
Currently this only applies to `chrome-visit-tab'.

All other operations always trigger a tab retrieval post-operation.")

(defvar chrome-buffer-name "*chrome-tabs*"
  "Name of buffer created to display tabs.")

(cl-defstruct (chrome-tab
               (:constructor chrome-tab-create)
               (:copier nil))
  (port      nil :read-only t)    ; Port of Chrome instance that contains this tab
  (host      nil :read-only t)    ; Host of Chrome instance that contains this tab
  (session   nil :read-only t)    ; DevTools session of this tab, currently (port . host)
  (id        nil :read-only t)    ; Unique id of tab in this Chrome instance
  (url       nil :read-only t)    ; URL of tab
  (title     nil :read-only t)    ; Title of tab
  is-deleted                      ; Is the tab in a deleted state?
  is-active                       ; Is tab selected in Chrome buffer?
  is-marked                       ; Is tab marked in Emacs?
  is-duplicate                    ; Is tab a dupicate of another? (based on URL)
  line)                           ; Tab line number in Chrome buffer


;;;
;;; Internal API
;;;


(defvar-local chrome--session-index nil
  "Hash table that contains indexed tabs (chrome-tab instances).

Keys are sessions, conses of form (post . host).
Values are conses of form:

  (tab-count . tab-list)")

(defvar-local chrome--cached-tabs nil
  "Hash table that contains indexed tabs (chrome-tab instances).

Keys are conses of form: (session . tab-id) where session is
a cons of form (port . host)

Values are chrome-tab instances.")

(defun chrome--reindex-tabs (tabs)
  "Index TABS into `chrome--session-index' and `chrome--cached-tabs'.
TABS must be an alist as returned from `chrome-get-tabs'."
  (clrhash chrome--session-index)
  (cl-loop
   for (session . tab-data) in tabs
   for port         = (car session)
   for host         = (cdr session)
   for tab-count    = 0
   for process-tabs = nil
   with seen-urls   = (make-hash-table :test 'equal)
   with tab-cache   = (make-hash-table :test 'equal)
   do
   (cl-loop
    for index from 0
    for tab in tab-data
    for tab-id     = (alist-get 'id tab)
    for url        = (alist-get 'url tab)
    for title      = (alist-get 'title tab)
    for cached-tab = (gethash (cons session tab-id) chrome--cached-tabs)
    for is-deleted = (and cached-tab (chrome-tab-is-deleted cached-tab))
    do
    ;; we want to retain is-deleted state on tabs until they're fully purged
    ;; we don't want to interrupt any other tab states so only recycle is-deleted
    ;; this also prevents deleted tabs from re-claiming is-active
    (let* ((tab (if is-deleted
                    cached-tab
                  (chrome-tab-create :port port :host host
                                     :session session
                                     :id tab-id :url url
                                     :title title
                                     :is-active (= index 0)))))
      (push tab process-tabs)
      (if (gethash url seen-urls)
          (setf (chrome-tab-is-duplicate tab) t)
        (puthash url t seen-urls))
      ;; update the local cache
      (puthash (cons session tab-id) tab tab-cache))
    finally (cl-incf tab-count index))
   ;; A hash table indexed by session containing all tabs
   (setf (gethash session chrome--session-index)
         (cons tab-count (nreverse process-tabs)))
   ;; update the global cache
   finally (setq chrome--cached-tabs tab-cache)))

(defvar-local chrome--visible-tabs nil)
(defvar-local chrome--marked-tabs 0)

(defun chrome--init-caches ()
  (setq chrome--session-index (make-hash-table :test 'equal)
        chrome--cached-tabs   (make-hash-table :test 'equal)
        chrome--visible-tabs  (make-hash-table)))

(defvar-local chrome--start-time nil)
(defvar-local chrome--elapsed-time nil)

(defun chrome--start-timer ()
  (unless chrome--start-time
    (setq chrome--start-time (current-time))))

(defun chrome--stop-timer ()
  (when chrome--start-time
    (setq chrome--elapsed-time
          (float-time (time-subtract
                       (current-time)
                       chrome--start-time))
          chrome--start-time nil)))

(cl-defmacro chrome--with-timing (&body body)
  (declare (indent defun))
  `(unwind-protect
       (progn
         (chrome--start-timer)
         ,@body)
     (chrome--stop-timer)
     (setq chrome--header-update t)))

(defun chrome--message (format-string &rest args)
  (let ((message-truncate-lines t))
    (message "chrome: %s" (apply #'format format-string args))))


;;;
;;; Filtering
;;;


(defvar-local chrome--active-filter nil)

(defvar-local chrome--last-tab nil)

(defsubst chrome--goto-line (line)
  (goto-char (point-min))
  (forward-line (1- line)))

(defsubst chrome--render-tab (tab &optional skip-goto)
  (unless skip-goto (chrome-goto-tab tab))
  (delete-region (line-beginning-position) (line-end-position))
  (insert (funcall chrome-render-function tab)))

(defsubst chrome--limit-tab (tab)
  (funcall chrome-limit-function tab))

(defsubst chrome--filter-tab (tab)
  (funcall chrome-filter-function tab))

(defun chrome--filter-tabs ()
  (when-let ((current-tab (chrome-current-tab)))
    (setq chrome--last-tab current-tab))
  (when (> (buffer-size) 0)
    (let ((inhibit-read-only t))
      (erase-buffer))
    (clrhash chrome--visible-tabs))
  (chrome--with-timing
    (cl-loop
     with active-tabs
     for session being the hash-keys of chrome--session-index
     for session-tabs = (cdr (gethash session chrome--session-index))
     with line        = 1
     do
     (cl-loop
      for tab in session-tabs do
      ;; Matching
      (if (and (chrome--limit-tab tab)
               (chrome--filter-tab tab))
          ;; Matches filter+limit
          (let ((inhibit-read-only t))
            (setf (chrome-tab-line tab) line
                  (gethash line chrome--visible-tabs) tab
                  line (1+ line))
            (chrome--render-tab tab t)
            (insert "\n")
            (when (chrome-tab-is-active tab) (push tab active-tabs)))
        ;; Doesn't match filter/limit
        (setf (chrome-tab-line tab) nil)))
     finally do
     ;; After all tabs have been filtered, determine where to set point
     (when (> line 1)
       ;; Previously selected tab if it's still visible and not deleted
       (if-let ((last-tab chrome--last-tab)
                (last-tab (gethash (cons (chrome-tab-session last-tab)
                                         (chrome-tab-id  last-tab))
                                   chrome--cached-tabs))
                (last-line (chrome-tab-line last-tab)))
           (chrome-goto-tab last-tab)
         ;; First active tab if there is one visible
         (if-let ((tab (car active-tabs)))
             (chrome-goto-tab tab)
           ;; Last tab
           (goto-char (point-max))
           (forward-line -1))))))
  (force-mode-line-update))


;;;
;;; Header
;;;


(defvar-local chrome--header-function #'chrome--header
  "Function that returns a string for tab view header line.")

(defun chrome--header-1 ()
  "Generate string for tab view header line."
  (let* ((total-tabs   (hash-table-count chrome--cached-tabs))
         (visible-tabs (hash-table-count chrome--visible-tabs))
         (total-procs  (hash-table-count chrome--session-index))
         (visible-procs
          (if (= visible-tabs total-tabs) total-procs
            (cl-loop
             for tab in (hash-table-values chrome--visible-tabs)
             with result = (make-hash-table :test 'equal)
             with count  = 0
             for session = (chrome-tab-session tab)
             unless (gethash session result)
             do (puthash session t result) (cl-incf count)
             when (= count total-procs) return count
             finally return count))))
    (cl-flet ((align (width str)
                     (let ((spec (format "%%%ds" width)))
                       (format spec str)))
              (size10 (x) (if (= x 0) 1 (1+ (floor (log x 10))))))
      (concat
       (align (+ 1 (* 2 (size10 total-tabs)))
              (propertize (format "%s/%s" visible-tabs total-tabs)
                          'help-echo "Visible / total tabs"))
       " "
       (align (size10 total-tabs)
              (propertize (int-to-string chrome--marked-tabs)
                          'help-echo "Marked tabs"
                          'face 'chrome-tab-marked-face))
       " "
       (align (1+ (* 2 (size10 total-procs)))
              (propertize (format "(%s/%s)" visible-procs total-procs)
                          'help-echo "Visible / total processes"))
       " "
       (format "By: %5s" (if (eq chrome-default-view :title) "title" "URL"))
       " "
       (format "Limit: %6s"
               (pcase chrome-default-limit
                 (:all    "all")
                 (:mark   "mark")
                 (:dup    "dup")
                 (:active "active")
                 (other (format "%s:%d" (cdr other) (car other)))))
       " "
       (when chrome-show-timing
         (propertize (format " %.4fs " chrome--elapsed-time)
                     'help-echo "Elapsed time for last operation"))
       (when-let ((filter (chrome-active-filter)))
         (format "Filter: %s"
                 (propertize filter
                             'help-echo "Search filter"
                             'face 'chrome-tab-filter-face)))))))

(defvar-local chrome--header-update nil)
(defvar-local chrome--header-cache nil)

(defun chrome--header ()
  "Return string for tab view header line.
If a previously cached string is still valid, it is returned.
Otherwise, a new string is generated and returned by calling
`chrome--header-1'."
  (if (and (null chrome--header-update)
           (eql (car chrome--header-cache) (buffer-modified-tick)))
      (cdr chrome--header-cache)
    (let ((header (chrome--header-1)))
      (prog1 header
        (setq chrome--header-cache (cons (buffer-modified-tick) header)
              chrome--header-update nil)))))


;;;
;;; Major mode
;;;


(defvar chrome-mode-map
  ;; Override self-insert-command with fallback to global-map
  (let* ((map        (make-keymap))
         (prefix-map (make-sparse-keymap))
         (char-table (cl-second map)))
    ;; Rebind keys that were bound to self-insert-command
    (map-keymap
     (lambda (event def)
       (when (eq def 'self-insert-command)
         (set-char-table-range
          char-table event 'chrome--self-insert-command)))
     global-map)
    ;; Standard bindings
    (define-key map (kbd "DEL")      'chrome--self-insert-command)
    (define-key map (kbd "C-l")      'chrome-retrieve-tabs)
    (define-key map (kbd "C-k")      'chrome-reset-filter)
    (define-key map (kbd "C-t")      'chrome-toggle-timing)
    (define-key map (kbd "C-w")      'chrome-copy-url)
    (define-key map (kbd "C-v")      'chrome-view-source)
    (define-key map (kbd "C-d")      'chrome-delete-tab)
    (define-key map (kbd "RET")      'chrome-visit-tab)
    (define-key map (kbd "M-m")      'chrome-mark-tab)
    (define-key map (kbd "M-d")      'chrome-delete-marked-tabs)
    (define-key map (kbd "M-M")      'chrome-mark-all-tabs)
    (define-key map (kbd "M-u")      'chrome-unmark-tab)
    (define-key map (kbd "M-U")      'chrome-unmark-all-tabs)
    (define-key map [(tab)]          'chrome-goto-active)
    (define-key map (kbd "C-<up>")   'previous-line)
    (define-key map (kbd "C-<down>") 'next-line)
    (define-key map (kbd "\\")       'chrome-toggle-url-view)
    ;; Prefix bindings
    (define-key map (kbd "/")         prefix-map)
    (define-key prefix-map (kbd "m") 'chrome-limit-marked)
    (define-key prefix-map (kbd "d") 'chrome-limit-dup)
    (define-key prefix-map (kbd "'") 'chrome-limit-session)
    (define-key prefix-map (kbd "a") 'chrome-limit-active)
    (define-key prefix-map (kbd "/") 'chrome-limit-none)
    map)
  "Keymap for chrome-mode.")

(defun chrome--self-insert-command ()
  (interactive)
  (let ((event last-input-event)
        updated)
    (cond ((characterp event)
           (if (and (= 127 event)
                    (not (display-graphic-p)))
               (pop chrome--active-filter)
             (push event chrome--active-filter))
           (setq updated t))
          ((eql event 'backspace)
           (pop chrome--active-filter)
           (setq updated t))
          (t (chrome--message "Unknown event %s" event)))
    (when updated (chrome--filter-tabs))))

(defun chrome-mode ()
  "Major mode for manipulating Google Chrome tabs.
\\<chrome-mode-map>
Tabs are retrieved from Chrome and displayed in an Emacs buffer, one tab
per line. Display takes place in ordered fashion, with tabs appearing as
they are in Chrome, older ones before newer ones.

Tabs can be further filtered in realtime by a user-specified regular
expression and limited by certain criteria described below. This mode tries
to remember point so that it keeps its associated tab selected across
filtering/limiting operations, assuming the tab is visible.

To minimize the feedback loop, this mode does not use the minibuffer
for input (e.g. when typing a filter regular expression).
You can start typing immediately and the filter updates, visible on
the header line.

Other than regular keys being bound to `chrome--self-insert-command',
the following commands are available:

Type \\[chrome-visit-tab] to switch to tab at point in Chrome. This brings Chrome
into focus and raises the window that contains the tab. With a prefix
argument, switch to the tab in Chrome but keep input focus in Emacs and
do not raise Chrome window.

Type \\[chrome-retrieve-tabs] to retrieve tabs from Chrome.
This wipes and recreates all tab state in Emacs but keeps the current
filter and limit.

Type \\[chrome-goto-active] to move point to the next active tab.
By repeatedly typing \\[chrome-goto-active], you can cycle through all active tabs.

Type \\[chrome-reset-filter] to kill the current filter.

Type \\[chrome-toggle-url-view] to toggle tabs being shown as titles or URLs.

Type \\[chrome-toggle-timing] to toggle timing information on the header line.

Type \\[chrome-copy-url] to copy URL belonging to tab at point.

Type \\[chrome-view-source] to view HTML source of tab at point in side buffer.
You need to enable `Allow JavaScript from Apple Events'
under View->Developer in Chrome to use this command.

Limiting tabs:

Type \\[chrome-limit-marked] to only show marked tabs.

Type \\[chrome-limit-dup] to only show duplicate tabs (by URL).

Type \\[chrome-limit-active] to only show active tabs (selected in Chrome).

Type \\[chrome-limit-session] to only show tabs belonging to a specific Chrome
session. Since you can't directly input the session, by repeatedly typing \\[chrome-limit-session]
you can cycle through all sessions.

Type \\[chrome-limit-none] to remove the current limit and show all tabs.

Marking and deleting:

Type \\[chrome-mark-tab] to mark tab at point.

Type \\[chrome-unmark-tab] to unmark tab at point.

Type \\[chrome-mark-all-tabs] to mark all tabs currently visible in Emacs.
If there is a region, only mark tabs in region.

Type \\[chrome-unmark-all-tabs] to unmark all tabs currently visible in Emacs.
If there is a region, only unmark tabs in region.

Type \\[chrome-delete-marked-tabs] to delete all marked tabs.

Type \\[chrome-delete-tab] to delete tab at point.

Deleting a single or all marked tabs always triggers a full
tab retrieval from Chrome.

\\{chrome-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (use-local-map chrome-mode-map)
  (font-lock-mode -1)
  (make-local-variable 'font-lock-function)
  (buffer-disable-undo)
  (setq major-mode 'chrome-mode
        mode-name "Chrome"
        truncate-lines t
        buffer-read-only t
        header-line-format '(:eval (funcall chrome--header-function))
        font-lock-function (lambda (_) nil))
  (chrome--init-caches)
  (chrome--with-timing
    (chrome--reindex-tabs (chrome-get-tabs))
    (chrome--filter-tabs))
  (hl-line-mode)
  (run-mode-hooks 'chrome-mode-hook))


;;;
;;; API
;;;


(defun chrome-active-filter ()
  "Return currently active filter string or nil."
  (when chrome--active-filter
    (apply 'string (reverse chrome--active-filter))))

(defun chrome-render-tab (tab)
  "Return string representation of TAB.
String is used as is to display TAB in `chrome-buffer-name' buffer.
It must not span more than one line but it may contain text properties."
  (let ((url        (chrome-tab-url tab))
        (title      (chrome-tab-title tab))
        (is-active  (chrome-tab-is-active tab))
        (is-marked  (chrome-tab-is-marked tab))
        (is-deleted (chrome-tab-is-deleted tab)))
    (let ((str (concat
                (if is-marked "* " "  ")
                (if (eq chrome-default-view :title)
                    (if (string-equal "" title) url title)
                  url))))
      (cond (is-deleted
             (setq str (propertize str 'face 'chrome-tab-deleted-face)))
            ((and is-marked is-active)
             (setq str (propertize str 'face 'chrome-tab-marked-active-face)))
            (is-marked
             (setq str (propertize str 'face 'chrome-tab-marked-face)))
            (is-active
             (setq str (propertize str 'face 'chrome-tab-active-face))))
      str)))

(defun chrome-limit-tab (tab)
  "Limits TAB by session, duplicate, marked or active status.
Limiting operation depends on `chrome-default-limit'."
  (cl-case chrome-default-limit
    (:all    t)
    (:mark   (chrome-tab-is-marked tab))
    (:dup    (chrome-tab-is-duplicate tab))
    (:active (chrome-tab-is-active tab))
    (t (equal chrome-default-limit (chrome-tab-session tab)))))

(defun chrome-filter-tab (tab)
  "Filters TAB using a case-insensitive match on either URL or title."
  (let ((filter (chrome-active-filter)))
    (or (null filter)
        (let ((case-fold-search t)
              (url   (chrome-tab-url tab))
              (title (chrome-tab-title tab)))
          (or (string-match (replace-regexp-in-string " " ".*" filter) url)
              (string-match (replace-regexp-in-string " " ".*" filter) title))))))

(defun chrome-current-tab ()
  "Return tab at point or nil."
  (gethash (line-number-at-pos (point))
           chrome--visible-tabs))

(defun chrome-goto-tab (tab)
  "Move point to TAB if it is visible."
  (when-let ((line (chrome-tab-line tab)))
    (chrome--goto-line line)))


;;;
;;; DevTools API
;;;


(defun chrome--get-tabs (port host)
  "Get tab state from a Chrome DevTools endpoint at HOST:PORT.

Return (tab-count . tab-list) where each tab in tab-list is an alist
with id, url, title keys."
  ;; xxx: needs error checking
  (let ((data (with-temp-buffer
                (url-insert-file-contents
                 (chrome-devtools-uri :verb "list" :host host :port port))
                (json-read))))
    (cl-loop with count = 0
             for tab-data across data
             for type    = (cdr (assoc 'type tab-data))
             for is-page = (equal type "page")
             when is-page do (cl-incf count)
             when is-page collect (list (assoc 'id    tab-data)
                                        (assoc 'url   tab-data)
                                        (assoc 'title tab-data))
             into tabs
             finally return (cons count tabs))))

(cl-defun chrome-devtools-uri (&key verb id (host "127.0.0.1") (port 9222))
  "Return a DevTools remote debugging VERB/ID uri."
  ;; anything this isn't an explicit verb is assumed to be an uri to visit
  (format "http://%s:%d/json/%s" host port
          (cond
           ;; verbs that take the id as an argument
           ((member verb '("close" "activate"))
            (format "%s/%s" verb id))
           ;; single verbs
           ((member verb '("list"))
            (format "%s" verb))
           ;; everything else is treated as a uri target
           (t
            (format "new?%s" verb)))))

(defun chrome-get-tabs ()
  "Return a record (alist) containing tab information.

The alist contains (session . tabs) pairs, where:

session is the currently active DevTools session, a cons of form (port . host)
tabs is a list of tabs, where each tab is an alist with id, url, title keys.

The first tab in the list of tabs is the active one."
  (cl-loop with tab-count     = 0
           with session-count = 0
           with error-count   = 0
           for session in chrome-sessions
           for total-sessions from 0
           for port = (car session)
           for host = (cdr session)
           for (cnt . tabs) = (condition-case err
                                  (chrome--get-tabs port host)
                                ('error
                                 (cl-incf error-count)
                                 (chrome--message "%s" (error-message-string err))
                                 nil))
           when cnt do (progn (cl-incf tab-count cnt)
                              (cl-incf session-count))
           when tabs collect (cons session tabs)
           finally (message "Retrieved %d tabs from %d sessions, %d sessions total%s"
                            tab-count session-count total-sessions
                            (if (> error-count 0)
                                (format ", %d sessions errored" error-count)
                              ""))))

(defsubst chrome--devtools-do (tab verb)
  (with-temp-buffer
    (url-insert-file-contents
     (chrome-devtools-uri
      :verb verb
      :id   (chrome-tab-id tab)
      :host (chrome-tab-host tab)
      :port (chrome-tab-port tab)))))

(defsubst chrome--delete (tab)
  ;; don't try to delete things that are already in purgatory
  (unless (chrome-tab-is-deleted tab)
    (chrome--devtools-do tab "close")
    ;; devtools is async on deletion so we have to maintain state on our end
    (setf (chrome-tab-is-deleted tab) t)))

(defsubst chrome--visit (tab)
  (chrome--devtools-do tab "activate"))

(defsubst chrome--view-source (tab)
  (chrome--devtools-do
   tab (format "view-source:%s" (chrome-tab-url tab))))

;;;
;;; Interactive
;;;

(defun chrome-reset ()
  "Reset the session state."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (setq-local chrome-sessions
              (default-value 'chrome-sessions))
  (chrome-retrieve-tabs)
  (message "All DevTools sessions reset"))

(defun chrome-connect ()
  "Add a session to the DevTools session state."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (let* ((host    (read-from-minibuffer "Host: " "127.0.0.1"))
         (port    (string-to-number (read-from-minibuffer "Port: " "9222")))
         (session (cons port host)))
    (if (member session chrome-sessions)
        (message "DevTools session %s:%d already exists" host port)
      (setq-local chrome-sessions (cons session chrome-sessions))
      (message "Added DevTools session %s:%d" host port)
      (chrome-retrieve-tabs))))

(defun chrome-toggle-timing ()
  "Toggle timing information on the header line."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (let ((timingp chrome-show-timing))
    (setq-local chrome-show-timing (if timingp nil t))
    (setq chrome--header-update t))
  (force-mode-line-update))

(defun chrome-toggle-url-view ()
  "Toggle tabs being displayed as titles or URLs."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (let ((view chrome-default-view))
    (setq-local chrome-default-view
                (if (eq view :title) :url :title)))
  (chrome--filter-tabs))

(defun chrome-limit-marked ()
  "Only show marked tabs."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (setq-local chrome-default-limit :mark)
  (chrome--filter-tabs))

(defun chrome-limit-session ()
  "Only show tabs belonging to a specific Chrome session.
Since you can't directly input the session, by repeatedly invoking this command
you can cycle through all sessions."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (let* ((limit chrome-default-limit)
         (sessions  (vconcat (hash-table-keys chrome--session-index)))
         (nsessions (length sessions)))
    (setq-local
     chrome-default-limit
     (aref sessions (if-let ((pos (cl-position limit sessions :test 'equal)))
                        (mod (1+ pos) nsessions)
                      0)))
    (chrome--filter-tabs)))

(defun chrome-limit-dup ()
  "Only show duplicate tabs (by URL)."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (setq-local chrome-default-limit :dup)
  (chrome--filter-tabs))

(defun chrome-limit-active ()
  "Only show active tabs (selected in Chrome)."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (setq-local chrome-default-limit :active)
  (chrome--filter-tabs))

(defun chrome-limit-none ()
  "Remove current limit and show all tabs."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (unless (eq :all chrome-default-limit)
    (setq-local chrome-default-limit :all)
    (chrome--filter-tabs)))

(defun chrome-copy-url ()
  "Copy URL belonging to tab at point."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (when-let ((tab (chrome-current-tab)))
    (let ((url (chrome-tab-url tab)))
      (kill-new url)
      (message "Copied: %s" url))))

(defun chrome-retrieve-tabs ()
  "Retrieve and filter all Chrome tabs.
This wipes and recreates all tab state in Emacs but keeps the current filter
and limit."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (chrome--with-timing
    (setq chrome--marked-tabs 0)
    (chrome--reindex-tabs (chrome-get-tabs))
    (chrome--filter-tabs)))

(defun chrome-reset-filter ()
  "Kill current tab filter."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (setq chrome--active-filter nil)
  (chrome--filter-tabs))

(defun chrome-delete-tab ()
  "Delete tab at point."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (when-let ((current-tab (chrome-current-tab)))
    (chrome--with-timing
      (condition-case err
          (chrome--delete current-tab)
        ('error
         (chrome--message "%s" (error-message-string err))
         (setf (chrome-tab-is-deleted current-tab) t)
         nil))
      (forward-line)
      (chrome-retrieve-tabs))))

(defun chrome-delete-marked-tabs ()
  "Delete all marked tabs."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (when (> chrome--marked-tabs 0)
    (chrome--with-timing
      (cl-loop
       for session being the hash-keys of chrome--session-index
       for session-tabs = (cdr (gethash session chrome--session-index)) do
       (cl-loop
        for tab in session-tabs
        when (chrome-tab-is-marked tab)
        collect tab into marked-tabs
        finally do
        (cl-loop for tab in marked-tabs do
                 (chrome--delete tab))))
      (chrome-retrieve-tabs))))

(defun chrome-mark-tab (&optional tab)
  "Mark tab at point."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (let ((move-forward (if tab nil t)))
    (when-let ((tab (or tab (chrome-current-tab))))
      (unless (chrome-tab-is-marked tab)
        (setf (chrome-tab-is-marked tab) t)
        (cl-incf chrome--marked-tabs)
        (let ((inhibit-read-only t)
              (point (point)))
          (unwind-protect
              (chrome--render-tab tab)
            (goto-char point))))
      (when move-forward (forward-line)))))

(defun chrome-unmark-tab (&optional tab)
  "Unmark tab at point."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (let ((move-forward (if tab nil t)))
    (when-let ((tab (or tab (chrome-current-tab))))
      (when (chrome-tab-is-marked tab)
        (setf (chrome-tab-is-marked tab) nil)
        (cl-decf chrome--marked-tabs)
        (let ((inhibit-read-only t)
              (point (point)))
          (unwind-protect
              (chrome--render-tab tab)
            (goto-char point))))
      (when move-forward (forward-line)))))

(defsubst chrome-do-visible-tabs (function)
  "Call FUNCTION once for each visible tab, passing tab as an argument."
  (mapc function
        (if (region-active-p)
            (save-excursion
              (let ((begin (region-beginning))
                    (end   (region-end)))
                (goto-char begin)
                (cl-loop for pos = (point) while (< pos end)
                         collect (chrome-current-tab)
                         do (forward-line))))
          (hash-table-values chrome--visible-tabs))))

(defun chrome-mark-all-tabs ()
  "Mark all tabs currently visible in Emacs.
If there is a region, only mark tabs in region."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (chrome-do-visible-tabs #'chrome-mark-tab))

(defun chrome-unmark-all-tabs ()
  "Unmark all tabs currently visible in Emacs.
If there is a region, only unmark tabs in region."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (chrome-do-visible-tabs #'chrome-unmark-tab))

(defun chrome-view-source ()
  "View HTML source of tab at point."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (when-let ((tab (chrome-current-tab)))
    (chrome--with-timing
      (let* ((strict-unpacking t))
        (chrome--view-source tab)))
    (force-mode-line-update)))

(defun chrome-visit-tab ()
  "Switch to tab at point in Chrome.
This brings Chrome into focus and raises the window that contains the tab."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (when-let ((current-tab (chrome-current-tab)))
    (chrome--with-timing
      (condition-case err
          (chrome--visit current-tab)
        ('error
         (chrome--message "%s" (error-message-string err))
         (message "Tab no longer exists.")
         (setf (chrome-tab-is-deleted current-tab) t)
         nil))
      (if chrome-auto-retrieve
          (chrome-retrieve-tabs)
        ;; Need to manually mark the current tab as active and the
        ;; previously active tab in this session as inactive then render both.
        (let ((pos     (point))
              (tab-id  (chrome-tab-id current-tab))
              (session (chrome-tab-session current-tab))
              (inhibit-read-only t))
          ;; Mark current tab as active and render it.
          (setf (chrome-tab-is-active current-tab) t)
          (chrome--render-tab current-tab t)
          ;; Search for previously active tab in this session, mark it as
          ;; inactive and if it's visible render it.
          (cl-loop for tab in (cdr (gethash session chrome--session-index))
                   when (and (not (eq current-tab tab))
                             (chrome-tab-is-active tab))
                   do
                   (setf (chrome-tab-is-active tab) nil)
                   (when (gethash (chrome-tab-line tab) chrome--visible-tabs)
                     (chrome--render-tab tab))
                   (cl-return))
          (goto-char pos))))))

(defun chrome-goto-active ()
  "Move point to the next active tab.
By repeatedly invoking this command, you can cycle through all active tabs."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (when (> (hash-table-count chrome--visible-tabs) 0)
    (cl-loop with pos   = (point)
             with tab   = (chrome-current-tab)
             with line  = (if tab (chrome-tab-line tab) 1)
             with start = (if tab (1+ line) line)
             with end   = (if tab line (save-excursion
                                         (goto-char (point-max))
                                         (line-number-at-pos)))
             ;; Starting either from the next line if a tab is selected
             ;; or beginning of buffer, scan each line for a tab that is
             ;; active. If an active tab is found, immediately return,
             ;; keeping it selected. If no active tab is found and the end
             ;; of the buffer is reached, start scanning from the beginning
             ;; until initial starting position is reached. If no active tab
             ;; is found, go to initial starting position and return.
             initially do (chrome--goto-line start)
             for current   = start then (1+ current)
             for maybe-tab = (chrome-current-tab)
             for is-active = (and maybe-tab (chrome-tab-is-active maybe-tab))
             while (/= current end) do
             (if maybe-tab
                 (if is-active (cl-return) (forward-line))
               ;; Reached end of buffer, start from beginning
               (setq current 0)
               (goto-char (point-min)))
             ;; No active tab found, go to starting position
             finally (goto-char pos))))

(defun chrome ()
  "Google Chrome remote tab control."
  (interactive)
  (let ((buf (get-buffer-create chrome-buffer-name)))
    (switch-to-buffer buf)
    (unless (eq major-mode 'chrome-mode)
      (chrome-mode))))

(provide 'chrome)
;;; chrome.el ends here
