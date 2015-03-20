// import necessary libraries
var acorn = require('acorn/acorn');
var acorn_loose = require('acorn/acorn_loose');
var walk = require('acorn/util/walk');
var util = require('util');
var absVal = require('./absVal');
var cGen = require('./cGen');


// global scope object
// will be assigned at pre-analysis stage
var globalScope = null;

function showUnfolded(obj) {
    console.log(util.inspect(obj, {depth: null}));
}

function Scope(paren) {
    this.paren = paren;
    this.variables = Object.create(null);
}

// Scope Object to represent scope of global, functions, and catch blocks
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
        ret = globalScope.variables[varName] = new absVal.AbsVal;
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


var scopeResolver = walk.make({

    Function: function (node, curScope, c) {
        var funcScope, parenScope = curScope;

        // Need to distinguish FunctionDeclaration and FunctionExpsression
        if (node.id) {
            // Since it has an identifier,
            // FunctionDeclaration: the scope is outer non-cactch scope.
            while (parenScope instanceof CatchScope)
                parenScope = parenScope.paren;
            // Register the named function to paren scope.
            parenScope.variables[node.id.name] = new absVal.AbsVal;
        } else {
            // FunctionExpsression, the scope is the enclosing scope.
            parenScope = curScope;
        }
        funcScope = new Scope(parenScope);
        // add function parameters to the scope
        for (var i = 0; i < node.params.length; i++) {
            var param = node.params[i];
            var name = param.name;
            funcScope.variables[name] = new absVal.AbsVal;
        }
        node.scope = funcScope;
        c(node.body, funcScope, undefined);
    },

    VariableDeclaration: function (node, curScope, c) {
        for (var i = 0; i < node.declarations.length; i++) {
            var decl = node.declarations[i];
            var name = decl.id.name;
            // console.log(name);
            // Find scope for the variable
            var varScope = curScope;
            while (varScope instanceof CatchScope
                   && !(name in varScope.variables)) {
                varScope = varScope.paren;
            }
            varScope.variables[name] = new absVal.AbsVal;
            if (decl.init) c(decl.init, curScope, undefined);
        }
    },

    TryStatement: function (node, curScope, c) {
        c(node.block, curScope, undefined);
        if (node.handler) {
            c(node.handler, curScope, undefined);
        }
        if (node.finalizer) {
            c(node.handler, curScope, undefined);
        }
    },

    CatchClause: function (node, curScope, c) {
        var catchScope = new CatchScope(curScope);
        catchScope.variables[node.param.name] = new absVal.AbsVal;
        node.scope = catchScope;
        c(node.body, catchScope, undefined);
    }
});


function analyze(input) {
    // the Scope object for global scope
    globalScope = new Scope(null);

    // parsing input program
    var ast = acorn_loose.parse_dammit(input);
    // Show AST before scope resolution
    showUnfolded(ast);

    // attatch the global scope to program node
    ast.scope = globalScope;

    // walk recursively to annotate scope objects and 
    // add variables to each scopes
    walk.recursive(ast, globalScope, null, scopeResolver);

    // After Scope Resolution
    console.log('\n\n[[After]]\n');
    showUnfolded(ast);

    var constraints = cGen.getConstraints(ast);

    console.log('\n\n[[Constraints]]\n');
    showUnfolded(constraints);
}

exports.analyze = analyze;
