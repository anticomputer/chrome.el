// This is free and unencumbered software released into the public domain.

function set_tab_multi(machine_url, pid, window_id, tab_id, raise)
{
    const se    = Application('System Events');
    const procs = se.applicationProcesses.whose({unixId: pid}).unixId.get();

    if (procs.length !== 0) {
        const chrome = Application(machine_url + '/?pid=' + pid);

        try {
            var window = chrome.windows.byId(window_id);
        } catch (_) {
            return {
                'error'      : 'Window not found',
                'error-data' : window_id,
            };
        }

        window.index   = 1;
        window.visible = true;

        var tabs = window.tabs.id.get();

        try {
            window.activeTabIndex = 1 + tabs.indexOf(tab_id);
        } catch (_) {
            return {
                'error'      : 'Tab not found',
                'error-data' : tab_id,
            };
        }

        if (raise === true) {
            if (chrome.windows.length === 1) {
                chrome.activate();
            } else {
                let proc = se.processes.whose({unixId: pid})[0];
                proc.windows[0].actions['AXRaise'].perform();
                proc.frontmost = true;
            }
        }

        return {};
    }

    return {
        'error'      : 'Process not found',
        'error-data' : pid,
    };
}
