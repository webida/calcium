var walk = require('acorn/dist/walk');
var fs = require('fs');
var infer = require('./infer');


// defining walker
var varFindingWalker = walk.make({
    Function: function(node, vb, c) {
        const innerVb = node.body['@block'];
        if (node.id) c(node.id, innerVb);
        for (var i = 0; i < node.params.length; i++)
            c(node.params[i], innerVb);
        c(node.body, innerVb);
    },
    TryStatement: function(node, vb, c) {
        c(node.block, vb);
        if (node.handler) {
            const catchVb = node.handler.body['@block'];
            c(node.handler.param, catchVb);
            c(node.handler.body, catchVb);
        }
        if (node.finalizer) {
            c(node.finalizer, vb);
        }
    },
    VariableDeclaration: function(node, vb, c) {
        for (var i = 0; i < node.declarations.length; ++i) {
            var decl = node.declarations[i];
            c(decl.id, vb);
            if (decl.init) c(decl.init, vb, "Expression");
        }
    }
});

function findIdentifierAt(ast, pos) {
    "use strict";

    // find the node
    var found = walk.findNodeAround(ast, pos, undefined,
        varFindingWalker, ast['@block']);
    if (found.node.type === 'Identifier') {
        return found;
    } else {
        return null;
    }
}
/**
 *
 * @param ast - scope annotated AST
 * @param {number} pos - character position
 * @returns {*} - array of AST nodes
 */
function findVarRefsAt(ast, pos) {
    "use strict";
    var found = findIdentifierAt(ast, pos);
    if (!found) {
        // pos is not at a variable
        return null;
    }
    // find refs for the id node
    var refs = findRefsToVariable(ast, found);

    return refs;
}

/**
 *
 * @param ast - scope annotated AST
 * @param found - node and varBlock of the variable
 * @returns {Array} - array of AST nodes
 */
function findRefsToVariable(ast, found) {
    "use strict";
    const varName = found.node.name;
    const vb1 = found.state.findVarInChain(varName);

    var refAddWalker = walk.make({
        Identifier: (node, vb, c) => {
            if (node.name !== varName) return;
            const vb2 = vb.findVarInChain(varName);
            if (vb1 === vb2) refs.push(node);
        }
    }, varFindingWalker);

    var refs = [];
    walk.recursive(ast, ast['@block'], refAddWalker);

    return refs;
}


// ============================================

function test() {
    "use strict";
    var test_pgm = fs.readFileSync('./tests/a.js');
    var result = infer.analyze(test_pgm, true);

    for (var i = 0; i < test_pgm.length; i++) {
        var foundNode = findIdentifierAt(result.AST, i);
        if (foundNode) {
            console.log(i, ': ', foundNode.name);
        }
    }
}

exports.findIdentifierAt = findIdentifierAt;
exports.findVarRefsAt = findVarRefsAt