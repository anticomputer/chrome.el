// This is free and unencumbered software released into the public domain.

function view_source_single(chrome_app_name, window_id, tab_id)
{
    const name  = chrome_app_name;
    const se    = Application('System Events');
    const procs = se.applicationProcesses.whose({name: name}).unixId.get();


    if (procs.length !== 0) {
        const chrome = Application(name);

        try {
            var window = chrome.windows.byId(window_id);
        } catch (_) {
            return {
                'error'      : 'Window not found',
                'error-data' : window_id,
            };
        }

        try {
            var tab = window.tabs.byId(tab_id);
        } catch (_) {
            return {
                'error'      : 'Tab not found',
                'error-data' : tab_id,
            };
        }

        const src = {javascript: "document.querySelector('html').outerHTML"};
        return {'html' : tab.execute(src)};
    }

    return {
        'error' : 'Process not found',
    };
}
