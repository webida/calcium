var walk = require('acorn/dist/walk');
var fs = require('fs');
var infer = require('./infer');


function findIdentifierNodeAt(ast, pos) {
    "use strict";

    // defining walker
    var searchWalker = walk.make({
        Function: function(node, st, c) {
            if (node.id) c(node.id, st);
            for (var i = 0; i < node.params.length; i++)
                c(node.params[i], st);
            c(node.body, st);
        },
        TryStatement: function(node, st, c) {
            c(node.block, st);
            if (node.handler) {
                c(node.handler.param, st);
                c(node.handler.body, st);
            }
            if (node.finalizer) {
                c(node.finalizer, st);
            }
        },
        VariableDeclaration: function(node, st, c) {
            for (var i = 0; i < node.declarations.length; ++i) {
                var decl = node.declarations[i];
                c(decl.id, st);
                if (decl.init) c(decl.init, st, "Expression");
            }
        }
    });

    // find the node
    var foundNode = walk.findNodeAround(ast, pos, undefined, searchWalker).node;
    if (foundNode.type === 'Identifier') {
        return foundNode;
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
function findIdRefsAt(ast, pos) {
    "use strict";
    var idNode = findIdentifierNodeAt(ast, pos);
    if (!idNode) {
        // pos is not at a variable
        return null;
    }
    // find refs for the id node
    var refs = findRefsToVariable(ast, idNode);

    return refs;
}

/**
 *
 * @param ast - scope annotated AST
 * @param idNode - identifier node of interest
 * @returns {Array} - array of AST nodes
 */
function findRefsToVariable(ast, idNode) {
    "use strict";
    var name = idNode.name;

    var refs = [];

    // TODO: find refs for the id
    return refs;
}


// ============================================

function test() {
    "use strict";
    var test_pgm = fs.readFileSync('./tests/a.js');
    var result = infer.analyze(test_pgm, true);

    for (var i = 0; i < test_pgm.length; i++) {
        var foundNode = findIdentifierNodeAt(result.AST, i);
        if (foundNode) {
            console.log(i, ': ', foundNode.name);
        }
    }
}

exports.findIdentifierNodeAt = findIdentifierNodeAt;