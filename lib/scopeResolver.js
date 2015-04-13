var absVal = require('./absVal');
var walk = require('acorn/util/walk');
var scope = require('./scope');

var scopeResolver = walk.make({

    Function: function (node, curScope, c) {
        var funcScope, parenScope = curScope, funcName;
        // Need to distinguish FunctionDeclaration and FunctionExpsression
        if (node.id) {
            // Since it has an identifier,
            // it is a FunctionDeclaration: the scope is outer non-cactch scope.
            funcName = node.id.name;
            while (parenScope instanceof scope.CatchScope)
                parenScope = parenScope.paren;
            // Register the named function to paren scope.
            var funcAbsVal
                = parenScope.variables[node.id.name] = new absVal.AbsVal;
        } else {
            // FunctionExpsression, the scope is the enclosing scope.
            funcName = '[do not know]';
            parenScope = curScope;
            // Note: we make AbsVal for FunctionExpressions next phase
        }
        // make a scope for function body
        funcScope = new scope.Scope(parenScope);
        node.scope = funcScope;

        var argNames = [];
        var argAbsVals = [];
        // add function parameters to the scope
        for (var i = 0; i < node.params.length; i++) {
            var paramName = node.params[i].name;
            var argAbsVal = new absVal.AbsVal;
            funcScope.variables[paramName] = argAbsVal;
            // collect for FnType
            argNames.push(paramName);
            argAbsVals.push(argAbsVal);
        }
        // make a FnType for the function
        var fnType = new absVal.FnType(funcName, argNames, argAbsVals);

        // For FunctionDeclaration,
        // add the fnType to AbsVal of the function's name
        if (node.id) {
            funcAbsVal.addType(fnType);
        }
        c(node.body, funcScope, undefined);
    },

    VariableDeclaration: function (node, curScope, c) {
        for (var i = 0; i < node.declarations.length; i++) {
            var decl = node.declarations[i];
            var name = decl.id.name;
            // console.log(name);
            // Find scope for the variable
            var varScope = curScope;
            while (varScope instanceof scope.CatchScope
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
        var catchScope = new scope.CatchScope(curScope);
        catchScope.variables[node.param.name] = new absVal.AbsVal;
        node.scope = catchScope;
        c(node.body, catchScope, undefined);
    }
});

exports.scopeResolver = scopeResolver;
