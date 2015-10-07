export const options = {
    acornOption: {
        ecmaVersion: 6,
        // sourceType: 'script' or 'module'
        // 'module' is used for ES6 modules and
        // 'use strict' assumed for those modules.
        // This option is also used by the analyzer.
        sourceType: 'script'
    },
    // At the start of program and each function,
    // check 'use strict'
    // maybe we do not need this option
    detectUseStrict: true,

    // 1 call-site sensitive
    sensitivityParameter: {
        maxDepthK: 1,
        /**
         * By default, we analyze all functions context-sensitively.
         * @param {FnType} fn
         * @returns {number}
         */
        contextLengthOfFunc: function (fn) {
            return 1;
        }
    }
};
