var walk = require('acorn/dist/walk');
var fs = require('fs');
var infer = require('./infer');

// a walker that visits each id with varBlock
var varWalker= walk.make({
    Function: function (node, vb, c) {
        const innerVb = node.body['@block'];
        if (node.id) c(node.id, innerVb);
        for (let i = 0; i < node.params.length; i++)
            c(node.params[i], innerVb);
        c(node.body, innerVb);
    },
    TryStatement: function (node, vb, c) {
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
    VariableDeclaration: function (node, vb, c) {
        for (let i = 0; i < node.declarations.length; ++i) {
            var decl = node.declarations[i];
            c(decl.id, vb);
            if (decl.init) c(decl.init, vb, "Expression");
        }
    }
});

/**
 *
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
 * @returns {*}
 */
function wrapWalker(walker, preNode, postNode) {
    const retWalker = {};
    // wrapping each function preNode and postNode
    for (let nodeType in walker) {
        if (!walker.hasOwnProperty(nodeType)) {
            continue;
        }
        retWalker[nodeType] = (node, vb, c) => {
            let ret;
            if (!preNode || preNode(node, vb, c)) {
                ret = walker[nodeType](node, vb, c);
            } else {
                return;
            }
            if (postNode) {
                ret = postNode(node, vb, c);
            }
            return ret;
        }
    }
    return retWalker;
}

function findIdentifierAt(ast, pos) {
    "use strict";

    function Found(node, state) {
        this.node = node;
        this.state = state;
    }

    // find the node
    const walker = wrapWalker(varWalker,
        (node, vb) => {
            if (node.start > pos || node.end < pos) {
                return false;
            }
            if (node.type === 'Identifier' && node.name !== '✖') {
                throw new Found(node, vb);
            }
            return true;
        });

    try {
        walk.recursive(ast, ast['@block'], walker);
    } catch (e) {
        if (e instanceof Found) {
            return e;
        } else {
            throw e;
        }
    }
    // identifier not found
    return null;
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
    const start = vb1.originNode.start;
    const end = vb1.originNode.end;
    const refs = [];

    var walker = walk.make({
        Identifier: (node, vb, c) => {
            if (node.name !== varName) return;
            const vb2 = vb.findVarInChain(varName);
            if (vb1 === vb2) refs.push(node);
        }
    }, varWalker);
    walker = wrapWalker(walker, (node, vb) => {
        // visit only related nodes
        return end >= node.start && node.end >= start;
    });

    walk.recursive(ast, ast['@block'], walker);
    return refs;
}

exports.findIdentifierAt = findIdentifierAt;
exports.findVarRefsAt = findVarRefsAt;