const walk = require('acorn/dist/walk');

/**
 * a walker that visits each id even though it is var declaration
 * the parameter vb denote varBlock
 */
const varWalker= walk.make({
    Function: function (node, vb, c) {
        'use strict';
        const innerVb = node.body['@block'];
        if (node.id) c(node.id, innerVb);
        for (let i = 0; i < node.params.length; i++)
            c(node.params[i], innerVb);
        c(node.body, innerVb);
    },
    TryStatement: function (node, vb, c) {
        c(node.block, vb);
        if (node.handler) {
            c(node.handler, vb);
        }
        if (node.finalizer) {
            c(node.finalizer, vb);
        }
    },
    CatchClause: function (node, vb, c) {
        const catchVb = node.body['@block'];
        c(node.param, catchVb);
        c(node.body, catchVb);
    },
    VariableDeclaration: function (node, vb, c) {
        'use strict';
        for (let i = 0; i < node.declarations.length; ++i) {
            const decl = node.declarations[i];
            c(decl.id, vb);
            if (decl.init) c(decl.init, vb);
        }
    },
    VariablePattern: function (node, vb, c) {
        'use strict';
        c(node, vb, 'Identifier');
    }
});

/**
 * Wrap a walker with pre- and post- actions
 *
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
 * @returns {*} - a new walker
 */
function wrapWalker(walker, preNode, postNode, stChange) {
    'use strict';
    const retWalker = {};
    // wrapping each function preNode and postNode
    for (let nodeType in walker) {
        if (!walker.hasOwnProperty(nodeType)) {
            continue;
        }
        retWalker[nodeType] = (node, st, c) => {
            let ret;
            let newSt = st;
            if (stChange) {
                newSt = stChange(node, st);
            }
            if (!preNode || preNode(node, newSt, c)) {
                ret = walker[nodeType](node, newSt, c);
            } else {
                return;
            }
            if (postNode) {
                ret = postNode(node, newSt, c);
            }
            return ret;
        }
    }
    return retWalker;
}


class Found {
    constructor(info) {
        this.info = info;
    }
}

function findIdentifierAt(ast, pos) {
    'use strict';

    // find the node
    const walker = wrapWalker(varWalker,
        (node, vb) => {
            if (node.start > pos || node.end < pos) {
                return false;
            }
            if (node.type === 'Identifier' && node.name !== '✖') {
                throw new Found({node: node, vb: vb});
            }
            return true;
        });

    try {
        walk.recursive(ast, ast['@block'], walker);
    } catch (e) {
        if (e instanceof Found) {
            return e.info;
        } else {
            throw e;
        }
    }
    // identifier not found
    return null;
}

function findSurroundingNode(ast, start, end) {
    'use strict';

    const walker = wrapWalker(varWalker,
        node => !(node.start > start || node.end < end),
        node => { throw new Found(node); }
    );

    try {
        walk.recursive(ast, undefined, walker);
    } catch (e) {
        if (e instanceof Found) {
            return e.info;
        } else {
            throw e;
        }
    }
    // node not found
    return null;
}

exports.Found = Found;
exports.wrapWalker = wrapWalker;
exports.varWalker = varWalker;
exports.findIdentifierAt = findIdentifierAt;
exports.findSurroundingNode = findSurroundingNode;