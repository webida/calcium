var absVal = require('./absVal');
var walk = require('acorn/util/walk');
var infer = require('./infer');


var constraints;

function getConstraints(ast) {
    // temporal set for generated constraints.
    constraints = [];

    recursiveWithReturn(ast, ast.scope, constraintGenerator);

    return constraints;
}

// constraint generating walker for expressions
var constraintGenerator = walk.make({

    Identifier: function (node, curScope, c) {
        // DEBUG
        // console.log(node.name);
        // console.log(curScope);
        return curScope.getAbsValOf(node.name);
    },

    AssignmentExpression: function (node, curScope, c) {
        if (node.left.type === 'MemberExpression') {
            // TODO
            // LHS is not a simple variable.
        } else {
            // LHS is a simple variable.
            var varName = node.left.name;
            var lhsAbsVal = curScope.getAbsValOf(varName);
            var rhsAbsVal = c(node.right, curScope, undefined);
            constraints.push({FROM: rhsAbsVal,
                              TO: lhsAbsVal});
            // corresponding AbsVal is the RHS
            return rhsAbsVal;
        }
    },

    Literal: function (node, curScope, c) {
        var res = new absVal.AbsVal;
        if (node.regex) {
            // not implemented yet
            // throw new Error('regex literal is not implemented yet');
            return res;
        }
        switch (typeof node.value) {
        case 'number':
            res.addType(absVal.PrimNumber);
            break;
        case 'string':
            res.addType(absVal.PrimString);
            break;
        case 'boolean':
            res.addType(absVal.PrimBoolean);
            break;
        case 'object':
            // I guess: Literal && object ==> node.value == null
            // null is ignored, so nothing to add
            break;
        case 'function':
            throw new Error('I guess function is impossible here.');
        }
        return res;
    },

    VariableDeclaration: function (node, curScope, c) {
        for (var i = 0; i < node.declarations.length; i++) {
            var decl = node.declarations[i];
            if (decl.init) {
                var lhsAbsVal = curScope.getAbsValOf(decl.id.name);
                var rhsAbsVal = c(decl.init, curScope, undefined);
                constraints.push({FROM: rhsAbsVal,
                                  TO: lhsAbsVal});
            }
        }
    },

    LogicalExpression: function (node, curScope, c) {
        var res = new absVal.AbsVal;
        var left = c(node.left, curScope, undefined);
        var right = c(node.right, curScope, undefined);
        constraints.push({FROM: left, TO: res},
                         {FROM: right, TO: res});
        return res;
    },

    ConditionalExpression: function (node, curScope, c) {
        var res = new absVal.AbsVal;
        c(node.test, curScope, undefined);
        var cons = c(node.consequent, curScope, undefined);
        var alt = c(node.alternate, curScope, undefined);
        constraints.push({FROM: cons, TO: res},
                         {FROM: alt, TO: res});
        return res;
    },
    
    CallExpression: function (node, curScope, c) {
        var res = new absVal.AbsVal;
        var args = [];

        // get AbsVals for each arguments
        for (var i = 0; i < node.arguments.length; i++) {
            args.push(
                c(node.arguments[i], curScope, undefined));
        }

        if (node.callee.type === 'MemberExpression') {
            // method call
            // TODO
        } else {
            // normal function call

        }
    }
});


function recursiveWithReturn(node, state, visitor) {
    function c(node, st, override) {
        return visitor[override || node.type](node, st, c);
    }
    return c(node, state);
}

exports.getConstraints = getConstraints;
