;;; chrome.el --- Google Chrome remote tab control -*- lexical-binding: t; -*-

;; Copyright (C) 2020 xristos@sdf.org
;;               2020 bas@anti.computer
;;
;; All rights reserved

;; Version: 0.5 - 2020-05-10
;; Author: xristos <xristos@sdf.org>
;;      Bas Alberts <bas@anti.computer>
;;
;; Maintainer: Bas Alberts <bas@anti.computer>
;; URL: https://github.com/anticomputer/...
;; Package-Requires: ((emacs "25"))
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

(defface chrome-tab-marked-active-face
  '((((class color) (background dark))  (:foreground "#ffffaa"))
    (((class color) (background light)) (:foreground "#800080")))
  ""
  :group 'chrome)

(defvar chrome-application-name "Google Chrome"
  "Name to use when retrieving application instance reference.
Change this if you are using Google Chrome Canary.")

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
 `chrome-limit-port-host'.")

(defvar chrome-auto-retrieve nil
  "If non-nil, retrieve all tabs after every operation.

Note that every retrieval recreates tab state in Emacs and thus discards
what was previously there (except filter and limit).
Currently this only applies to `chrome-visit-tab'.

Delete operations always trigger a tab retrieval post-operation.")

(defvar chrome-script-directory
  (and load-file-name
       (concat (file-name-directory load-file-name)
               (file-name-as-directory "scripts")))
  "Directory that contains JXA Chrome control scripts.
Set this manually if auto-detection fails.")

(cl-defstruct (chrome-tab
               (:constructor chrome-tab-create)
               (:copier nil))
  (port-host nil :read-only t)    ; (PORT . HOST) of Chrome instance that contains this tab
  (id        nil :read-only t)    ; Unique id of tab in this Chrome instance
  (window-id nil :read-only t)    ; Unique id of window that contains this tab
  (url       nil :read-only t)    ; URL of tab
  (title     nil :read-only t)    ; Title of tab
  is-active                       ; Is tab selected in Chrome buffer?
  is-marked                       ; Is tab marked in Emacs?
  is-duplicate                    ; Is tab a dupicate of another? (based on URL)
  line)                           ; Tab line number in Chrome buffer


;;;
;;; Internal API
;;;


(defvar-local chrome--process-index nil
  "Hash table that contains indexed tabs (chrome-tab instances).

Keys are pairs of (PORT . HOST).
Values are conses of form:

  ((tab-count . window-count) tab-list)

Tabs in tab-list are ordered as they appear in Chrome:
Older tabs before newer tabs.")

(defvar-local chrome--cached-tabs nil
  "Hash table that contains indexed tabs (chrome-tab instances).

Keys are conses of form: (port-host . tab-id)
Values are chrome-tab instances.")

(defun chrome--reindex-tabs (tabs)
  "Index TABS into `chrome--process-index' and `chrome--cached-tabs'.
TABS must be an alist as returned from `chrome-get-tabs'."
  (clrhash chrome--process-index)
  (clrhash chrome--cached-tabs)
  (cl-loop
   for (port-host . data) in (cdr tabs)
   for windows            = (aref data 0)
   for active-tab-windows = (aref data 1)
   for tab-id-windows     = (aref (aref data 2) 0)
   for url-windows        = (aref (aref data 2) 1)
   for title-windows      = (aref (aref data 2) 2)
   for process-tabs       = nil
   for tab-count          = 0
   for window-count       = 0
   with seen-urls         = (make-hash-table :test 'equal)
   do
   (cl-loop
    for window-id     across windows
    for active-tab-id across active-tab-windows
    for tab-ids       across tab-id-windows
    for urls          across url-windows
    for titles        across title-windows do
    (cl-incf window-count)
    (cl-loop
     for tab-id across tab-ids
     for url    across urls
     for title  across titles do
     (let ((tab (chrome-tab-create :port-host port-host :id tab-id :url url
                                   :title title
                                   :window-id window-id
                                   :is-active (string= tab-id active-tab-id))))
       (push tab process-tabs)
       (cl-incf tab-count)
       (if (gethash url seen-urls)
           (setf (chrome-tab-is-duplicate tab) t)
         (puthash url t seen-urls))
       (puthash (cons port-host tab-id) tab chrome--cached-tabs))))
   ;; A hash table indexed by port-host containing all tabs
   (setf (gethash port-host chrome--process-index)
         (cons (cons tab-count window-count)
               (nreverse process-tabs)))))

(defvar-local chrome--visible-tabs nil)
(defvar-local chrome--marked-tabs 0)

(defun chrome--init-caches ()
  (setq chrome--process-index (make-hash-table)
        chrome--visible-tabs  (make-hash-table)
        chrome--cached-tabs   (make-hash-table :test 'equal)))

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

(cl-defmacro chrome--check-error ((res) call &body body)
  (declare (indent defun))
  (let ((err      (cl-gensym))
        (err-data (cl-gensym)))
    `(let* ((strict-unpacking t)
            (,res ,call))
       (if-let ((,err       (cdr (assoc "error" ,res))))
           (let ((,err-data (cdr (assoc "error-data" ,res))))
             (chrome--message "%s%s" ,err
                              (if ,err-data
                                  (format " [%s]" ,err-data)
                                "")))
         ,@body))))


;;;
;;; Filtering
;;;


(defvar-local chrome--active-filter nil)

(defun chrome--find-script (name)
  (unless chrome-script-directory
    (error "Script directory is unset (chrome-script-directory)"))
  (concat chrome-script-directory name))

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
     for port-host being the hash-keys of chrome--process-index
     with line        = 1
     for process-tabs = (gethash port-host chrome--process-index)
     for tabs         = (cdr process-tabs) do
     (cl-loop
      for tab in tabs do
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
                (last-tab (gethash (cons (chrome-tab-port-host last-tab)
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
         (total-procs  (hash-table-count chrome--process-index))
         (visible-procs
          (if (= visible-tabs total-tabs) total-procs
            (cl-loop with result and count = 0
                     for tab in (hash-table-values chrome--visible-tabs)
                     for port-host = (chrome-tab-port-host tab)
                     unless (memq port-host result)
                     do (push port-host result) (cl-incf count)
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
                 (other other)))
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
    (define-key prefix-map (kbd "'") 'chrome-limit-port-host)
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

Type \\[chrome-limit-port-host] to only show tabs belonging to a specific Chrome
instance by PORT-HOST. Since you can't directly input the PORT-HOST,
by repeatedly typing \\[chrome-limit-port-host] you can cycle through all PORT-HOSTs.

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
String is used as is to display TAB in *chrome-tabs* buffer.
It must not span more than one line but it may contain text properties."
  (let ((url       (chrome-tab-url tab))
        (title     (chrome-tab-title tab))
        (is-active (chrome-tab-is-active tab))
        (is-marked (chrome-tab-is-marked tab)))
    (let ((str (concat
                (if is-marked "* " "  ")
                (if (eq chrome-default-view :title)
                    (if (string-equal "" title) url title)
                  url))))
      (cond ((and is-marked is-active)
             (setq str (propertize str 'face 'chrome-tab-marked-active-face)))
            (is-marked
             (setq str (propertize str 'face 'chrome-tab-marked-face)))
            (is-active
             (setq str (propertize str 'face 'chrome-tab-active-face))))
      str)))

(defun chrome-limit-tab (tab)
  "Limits TAB by port-host, duplicate, marked or active status.
Limiting operation depends on `chrome-default-limit'."
  (cl-case chrome-default-limit
    (:all    t)
    (:mark   (chrome-tab-is-marked tab))
    (:dup    (chrome-tab-is-duplicate tab))
    (:active (chrome-tab-is-active tab))
    (t (equal chrome-default-limit (chrome-tab-port-host tab)))))

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
;;; Devtools API versions of the chrome tab functions
;;;

;; a list of chrome sessions with remote debugging ports
(defvar chrome--devtools-sessions '((9222 . "127.0.0.1"))
  "A list of devtools sessions which are pairs of (port . host).

You can enable a devtools remote debugging port for Chrome with:

--remote-debugging-port=9222

Note that anyone who can send direct, or indirect, requests to this
localhost port can drive, inspect, and otherwise influence your Chrome
session.")

(defun chrome--devtools-default-session ()
  (car chrome--devtools-sessions))

(defun chrome--devtools-get-tabs (host port)
  "Pull the current tab state from a devtools remote debugger at HOST:PORT."
  ;; xxx: needs error checking
  (with-temp-buffer
    (url-insert-file-contents
     (chrome-devtools-uri :verb "list"
                          :host host
                          :port port))
    (let ((data (json-read)))
      (cl-loop for tab-data across data
               for tab-idx from 0
               when (equal (cdr (assoc 'type tab-data)) "page")
               collect
               (list (cdr (assoc 'id tab-data))
                     (cdr (assoc 'url tab-data))
                     (cdr (assoc 'title tab-data)))
               into devtabs
               finally return (cons tab-idx devtabs)))))

(cl-defun chrome-devtools-uri (&key verb id (host "127.0.0.1") (port 9222))
  "Return a devtools remote debugging VERB/ID uri."
  (let* ((action
          (if id
              (format "%s/%s" verb id)
            verb))
         (uri (format "http://%s:%d/json/%s" host port action)))
    uri))

(defun chrome-get-tabs ()
  "Return a record (alist) containing tab information.

The alist contains (port-host . [window-ids, active-tab-ids, tabs]) pairs,
where:

port-host is a pair of (port . host)

window-ids and active-tab-ids are vectors of length 1, and port
represents the currently active devtools debug port.

tabs is a vector of 3 elements: [[tab-ids], [urls], [titles]] where
tab-ids, urls and titles are vectors of same length.
"

  (let ((tab-record '()))
    (dolist (session chrome--devtools-sessions)
      ;; we treat tabs for a single devtools host:port as belonging to a virtual window with id 0
      (let* ((port (car session))
             (host (cdr session))
             (devtools-window-id 0)
             (tab-collect (chrome--devtools-get-tabs host port))
             (obj-count (car tab-collect))
             (devtabs (cdr tab-collect))
             (window-ids (vector devtools-window-id))
             ;; the first tab in our tabs list is the only active tab we can determine, so use that
             (active-tab-ids (vector (caar devtabs)))
             (tab-ids (vconcat (mapcar #'(lambda (tab) (car tab)) devtabs)))
             (tab-urls (vconcat (mapcar #'(lambda (tab) (cadr tab)) devtabs)))
             (tab-titles (vconcat (mapcar #'(lambda (tab) (caddr tab)) devtabs)))
             ;; we pretend that we have a single window of id 0 that contains everything
             (tabs-vect (vector
                         (vector tab-ids)
                         (vector tab-urls)
                         (vector tab-titles))))
        (message "Fetched %d tabs from devtools://%s:%d" (length devtabs) host port)
        ;; we use the devtools port as an identifier, which is expected to be a string in the indexer
        (cl-pushnew (cons (cons port host)
                          (vector window-ids active-tab-ids tabs-vect))
                    tab-record)))
    (cons :reco tab-record)))

(defun chrome--devtools-apply-verb (host port tab-ids verb)
  (mapcar #'(lambda (id)
              (with-temp-buffer
                (url-insert-file-contents
                 (chrome-devtools-uri
                  :verb verb
                  :id id
                  :host host
                  :port port))))
          ;; this is a vector of tab-id
          tab-ids)
  ;; xxx: errors are returned as an alist with ("error" . xxx) ("error-data" . xxx) pairs
  nil)

(defun chrome--devtools-delete (host port tab-vect)
  (chrome--devtools-apply-verb host port tab-vect "close")
  ;; xxx: devtools sometimes responds before the tab is gone
  (chrome-retrieve-tabs)
  ;; xxx: errors should go here as well
  (list (cons "count" (length tab-vect))))

(defsubst chrome--delete-multi (port-host tab-ids)
  (let ((tab-vect (cdadr tab-ids)))
    (chrome--devtools-delete
     (cdr port-host)
     (car port-host)
     tab-vect)))

(defsubst chrome--visit-tab-multi (port-host window-id tab-id noraise)
  ;; we ignore noraise and window-id, not needed for us yet
  (chrome--devtools-apply-verb
   (cdr port-host)
   (car port-host)
   (vector tab-id)
   "activate"))

(defun chrome--tab-from-id (port-host tab-id)
  (gethash (cons port-host tab-id) chrome--cached-tabs))

(defsubst chrome--view-source-multi (port-host window-id tab-id)
  (let ((tab (chrome--tab-from-id port-host tab-id)))
    (when tab
      (chrome--devtools-apply-verb
       (cdr port-host)
       (car port-host)
       (vector nil)
       (format "new?view-source:%s" (chrome-tab-url tab))))))

;;;
;;; Interactive
;;;

(defun chrome-reset ()
  "Reset the session state."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (setq chrome--devtools-sessions '())
  (chrome-retrieve-tabs)
  (message "Reset all devtools sessions"))

(defun chrome-connect ()
  "Add a session to the devtools session state."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (let ((host (read-from-minibuffer "host: " "127.0.0.1"))
        (port (string-to-number (read-from-minibuffer "port: " "9222"))))
    (cl-pushnew (cons port host) chrome--devtools-sessions)
    (message "Added devtools session %s:%d" host port)
    (chrome-retrieve-tabs)))

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

(defun chrome-limit-port-host ()
  "Only show tabs belonging to a specific Chrome instance, by PORT-HOST.
Since you can't directly input the PORT-HOST, by repeatedly invoking this command
you can cycle through all PORT-HOSTs."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (let* ((limit chrome-default-limit)
         (port-hosts (cl-loop for port-host in (hash-table-keys chrome--process-index)
                              vconcat (list port-host)))
         (nport-hosts (length port-hosts)))
    (setq-local chrome-default-limit
                (aref port-hosts (if-let ((pos (cl-position limit port-hosts)))
                                     (mod (1+ pos) nport-hosts)
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
  (when-let ((tab (chrome-current-tab)))
    (let* ((port-host (chrome-tab-port-host tab))
           (tab-id    (chrome-tab-id tab))
           (window-id (chrome-tab-window-id tab))
           (tab-ids   (list :reco (cons window-id (vector tab-id)))))
      (chrome--with-timing
        (chrome--check-error (ret)
          (chrome--delete-multi port-host tab-ids)
          (forward-line)
          (chrome-retrieve-tabs)
          (message "Deleted %d tabs" (cdr (assoc "count" ret))))))))

(defun chrome-delete-marked-tabs ()
  "Delete all marked tabs."
  (interactive)
  (cl-assert (eq major-mode 'chrome-mode) t)
  (when (> chrome--marked-tabs 0)
    (chrome--with-timing
      (cl-loop
       for port-host being the hash-keys of chrome--process-index
       for process-tabs = (cdr (gethash port-host chrome--process-index))
       for grouped-tabs = nil do
       (cl-loop for tab in process-tabs
                when (chrome-tab-is-marked tab) do
                (let ((window-id (chrome-tab-window-id tab)))
                  (push (chrome-tab-id tab)
                        (alist-get window-id grouped-tabs)))
                finally do
                (setq grouped-tabs
                      (cons :reco
                            (mapcar (lambda (c) (cons (car c) (vconcat (cdr c))))
                                    grouped-tabs)))
                (chrome--check-error (ret)
                  (chrome--delete-multi port-host grouped-tabs)
                  (chrome-retrieve-tabs)
                  (message "Deleted %d tabs" (cdr (assoc "count" ret)))))))))

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
      (let* ((strict-unpacking t)
             (window-id (chrome-tab-window-id tab))
             (tab-id    (chrome-tab-id tab))
             (port-host (chrome-tab-port-host tab)))
        (chrome--check-error (ret)
          (chrome--view-source-multi port-host window-id tab-id)
          ;; (let ((buf (get-buffer-create "*chrome-source*")))
          ;;   (with-current-buffer buf
          ;;     (erase-buffer)
          ;;     (insert (cdr (assoc "html" ret)))
          ;;     (goto-char (point-min)))
          ;;   (display-buffer buf))
          )))
    (force-mode-line-update)))

(defun chrome-visit-tab (&optional noraise)
  "Switch to tab at point in Chrome.
This brings Chrome into focus and raises the window that contains the tab.
With a prefix argument, switch to the tab in Chrome but keep input focus in
Emacs and do not raise Chrome window."
  (interactive "P")
  (cl-assert (eq major-mode 'chrome-mode) t)
  (when-let ((tab (chrome-current-tab)))
    (chrome--with-timing
      (let* ((window-id (chrome-tab-window-id tab))
             (tab-id    (chrome-tab-id tab))
             (port-host (chrome-tab-port-host tab)))
        (chrome--check-error (ret)
          (chrome--visit-tab-multi port-host window-id tab-id noraise)
          (when-let ((warn (cdr (assoc "warn" ret))))
            (chrome--message "%s" warn))
          (if chrome-auto-retrieve (chrome-retrieve-tabs)
            ;; Need to manually mark the current tab as active and the
            ;; previously active tab in this window as inactive then render
            ;; both of them.
            (let ((pos (point))
                  (inhibit-read-only t))
              ;; Mark current tab as active and render it.
              (setf (chrome-tab-is-active tab) t)
              (chrome--render-tab tab t)
              ;; Search for previously active tab in this window, mark it as
              ;; inactive and if it's visible render it.
              (cl-loop for tab in (cdr (gethash port-host chrome--process-index))
                       for tid = (chrome-tab-id tab)
                       for wid = (chrome-tab-window-id tab) do
                       (when (and (= wid window-id)
                                  ;; Skip currently active tab
                                  (not (string= tid tab-id))
                                  (chrome-tab-is-active tab))
                         (setf (chrome-tab-is-active tab) nil)
                         (when (gethash (chrome-tab-line tab)
                                        chrome--visible-tabs)
                           (chrome--render-tab tab))
                         (cl-return)))
              (goto-char pos))))))))

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
  (let ((buf (get-buffer-create "*chrome-tabs*")))
    (switch-to-buffer buf)
    (unless (eq major-mode 'chrome-mode)
      (chrome-mode))))

(provide 'chrome)
;;; chrome.el ends here
