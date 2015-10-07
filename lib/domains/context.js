// Context for k-CFA analysis
//
// Assume a context is an array of numbers.
// A number in such list denotes a call site, that is @label of a CallExpression.
// We keep the most recent 'k' call-sites.
// Equality on contexts should look into the numbers.

export const sensitivityParameter = {
    // maximum length of context
    maxDepthK: 0,
    //
    contextLengthOfFunc: function (fn) {
        return 0;
    }
};

export function changeSensitivityParameter(param) {
    sensitivityParameter.maxDepthK = param.maxDepthK;
    sensitivityParameter.contextLengthOfFunc = param.contextLengthOfFunc;
}

// Functional objects for call-site context
export class CallSiteContext {

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
     * A private method for context equality
     * @param list - array composed of context elements
     * @returns {boolean}
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
     * Return the context which is myself + callSite.
     * If I am nullContext, the result is myself.
     * @param callSite - a call-site to append
     * @returns {CallSiteContext}
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
     * @returns {CallSiteContext}
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

    toString() {
        return this.csList.toString();
    }
}

// Declaring class fields for CallSiteContext
CallSiteContext.contextPool = new Set();
// nullContext is for functions that never be called
CallSiteContext.nullContext = new CallSiteContext(null);
// epsilonContext is for context of length 0
CallSiteContext.epsilonContext = new CallSiteContext([]);
