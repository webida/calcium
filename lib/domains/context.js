/**
 * @file Defines context for k-CFA analysis
 * @author sewon326.kim@samsung.com
 */


/**
 * Initial sensitivity parameter.
 * @type {{maxDepthK: number, contextLengthOfFunc: sensitivityParameter.contextLengthOfFunc}}
 */
export const sensitivityParameter = {
    // maximum length of context
    maxDepthK: 0,
    //
    contextLengthOfFunc: function (fn) {
        return 0;
    }
};

/**
 * Changes the sensitivity parameter.
 * @param param
 */
export function changeSensitivityParameter(param) {
    sensitivityParameter.maxDepthK = param.maxDepthK;
    sensitivityParameter.contextLengthOfFunc = param.contextLengthOfFunc;
}

export class CallSiteContext {
    /**
     * Construct a CallSiteContext from `list`.
     * @param list
     */
    constructor(list) {
        for (let ctx of CallSiteContext.contextPool.values()) {
            if (ctx._hasSameList(list)) {
                // use existing context
                return ctx;
            }
        }
        // clone the given list
        if (list === null) {
            this.csList = null;
        } else {
            this.csList = list.slice(0);
        }
        // add the current instance to the pool
        CallSiteContext.contextPool.add(this);
    }

    /**
     * Check whether the list represent the same context.
     * @private
     * @param list - array composed of context elements
     * @return {boolean}
     */
    _hasSameList(list) {
        if (this.csList === null) {
            return list === null;
        }
        if (list === null) {
            return this.csList === null;
        }
        if (this.csList.length !== list.length) {
            return false;
        }
        for (let i = 0; i < this.csList.length; i++) {
            if (this.csList[i] !== list[i]) return false;
        }
        return true;
    }

    /**
     * Returns the context which is myself + callSite.
     * If I am nullContext, the result is myself.
     * @param callSite - a call-site to append
     * @return {CallSiteContext}
     */
    appendOne(callSite) {
        // if null context, result is itself
        if (this === CallSiteContext.nullContext) {
            return this;
        }
        // use concat to create a new array
        // oldest one comes first
        const appended = this.csList.concat(callSite);
        if (appended.length > sensitivityParameter.maxDepthK) {
            appended.shift();
        }
        return new CallSiteContext(appended);
    }

    /**
     * Truncate context according to the given function.
     * @param {FnType} fn
     * @return {CallSiteContext}
     */
    truncateFor(fn) {
        // for nullContext,
        if (this === CallSiteContext.nullContext) {
            return this;
        }
        // compute the length of the context
        const contextLength = sensitivityParameter.contextLengthOfFunc(fn);
        if (contextLength === 0) {
            // context of length 0
            return CallSiteContext.epsilonContext;
        } else {
            // choose last several call-sites
            return new CallSiteContext(this.csList.slice(-contextLength));
        }
    }

    /**
     * Returns the string representation
     * @return {string}
     */
    toString() {
        return this.csList.toString();
    }
}

/**
 * Declaring class fields for CallSiteContext
 * @static
 */
CallSiteContext.contextPool = new Set();

/**
 * nullContext is for functions that never be called
 * @static
 */
CallSiteContext.nullContext = new CallSiteContext(null);

/**
 * epsilonContext is for context of length 0
 * @static
 */
CallSiteContext.epsilonContext = new CallSiteContext([]);
