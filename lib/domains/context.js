// Context for k-CFA analysis
//
// Assume a context is an array of numbers.
// A number in such list denotes a call site, that is @label of a CallExpression.
// We keep the most recent 'k' call-sites.
// Equality on contexts should look into the numbers.

export const callSiteContextParameter = {
    // maximum length of context
    maxDepthK: 0,
    // function list for sensitive analysis
    sensFuncs: {}
};

// Functional objects for call-site context
export class CallSiteContext {

    constructor(list) {
        for (let ctx of CallSiteContext.contextPool.values()) {
            if (ctx.hasSameList(list)) {
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
    hasSameList(list) {
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

    appendOne(callSite) {
        // use concat to create a new array
        // oldest one comes first
        const appended = this.csList.concat(callSite);
        if (appended.length > callSiteContextParameter.maxDepthK) {
            appended.shift();
        }
        return new CallSiteContext(appended);
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
