var absVal = require('./absVal');

function Scope(paren) {
    this.paren = paren;
    this.variables = Object.create(null);
}

// global scope object
// will be assigned at pre-analysis stage
Scope.prototype.globalScope = null;

Scope.prototype = Object.create(null);
Scope.prototype.getVars = function() {
    return Object.getOwnPropertyNames(this.variables);
};
Scope.prototype.getAbsValOf = function(varName) {
    var scope = this;
    var ret;
    while (scope && scope.getVars().indexOf(varName) === -1) {
        console.log(scope.getVars());
        scope = scope.paren;
    }
    // when the variable is free in the program
    if (scope === null) {
        // it belongs to the global scope.
        ret = Scope.globalScope.variables[varName] = new absVal.AbsVal;
    } else {
        // otherwise get it from the given Scope
        ret = scope.variables[varName];
    }
    return ret;
};

function CatchScope(paren) {
    Scope.call(this, paren);
}
CatchScope.prototype = Object.create(new Scope);


exports.Scope = Scope;
exports.CatchScope = CatchScope;
