// Context for k-CFA analysis
//
// Assume a context is an array of numbers.
// A number in such list denotes a call site, that is @label of a CallExpression.
// We keep the most recent 'k' callsites.
// Equality on contexts should look into the numbers.

export const callSiteContextParameter = {
    // maximum length of context
    maxDepthK: 0,
    // function list for sensitive analysis
    sensFuncs: {}
};

export class CallSiteContext {

    constructor(csList) {
        if (csList) this.csList = csList;
        else this.csList = [];
    }

    equals(other) {
        if (this.csList.length != other.csList.length) return false;
        for (var i = 0; i < this.csList.length; i++) {
            if (this.csList[i] !== other.csList[i]) return false;
        }
        return true;
    }

    appendOne(callSite) {
        // use concat to create a new array
        // oldest one comes first
        var appended = this.csList.concat(callSite);
        if (appended.length > callSiteContextParameter.maxDepthK) {
            appended.shift();
        }
        return new CallSiteContext(appended);
    }

    toString() {
        return this.csList.toString();
    }
}
