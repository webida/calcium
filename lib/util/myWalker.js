const walk = require('acorn/dist/walk');

/**
 * a walker that visits each id even though it is var declaration
 * the parameter vb denote varBlock
 */
const varWalker= walk.make({
    Function: (node, vb, c) => {
        'use strict';
        const innerVb = node.body['@block'];
        if (node.id) c(node.id, innerVb);
        for (let i = 0; i < node.params.length; i++)
            c(node.params[i], innerVb);
        c(node.body, innerVb);
    },
    TryStatement: (node, vb, c) => {
        c(node.block, vb);
        if (node.handler) {
            c(node.handler, vb);
        }
        if (node.finalizer) {
            c(node.finalizer, vb);
        }
    },
    CatchClause: (node, vb, c) => {
        const catchVb = node.body['@block'];
        c(node.param, catchVb);
        c(node.body, catchVb);
    },
    VariableDeclaration: (node, vb, c) => {
        for (let i = 0; i < node.declarations.length; ++i) {
            const decl = node.declarations[i];
            c(decl.id, vb);
            if (decl.init) c(decl.init, vb);
        }
    },
    VariablePattern: (node, vb, c) => {
        c(node, vb, 'Identifier');
    }
});

/**
 * Wrap a walker with pre- and post- actions
 *
 * @param walker - base walker
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
 * @param stChange - state change function
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

/**
 * A utility class for searching ASTs.
 * We use info to record any useful information.
 */
class Found {
    constructor(info) {
        this.info = info;
    }
}

function findIdentifierAt(ast, pos) {
    'use strict';
    return findNodeAt(ast, pos,
            node => node.type === 'Identifier' && node.name !== '✖'
    );
}

function findMemberOrVariableAt(ast, pos) {
    'use strict';
    return findNodeAt(ast, pos,
            node => (node.type === 'Identifier' && node.name !== '✖')
        || (node.type === 'MemberExpression')
    );
}

/**
 * Find a node at pos.
 * If found, it also returns its varBlock.
 * If not found, return null.
 * @param ast - AST node
 * @param pos - index position
 * @param nodeTest - Check whether the node is what we are looking for
 * @returns {*}
 */
function findNodeAt(ast, pos, nodeTest) {
    'use strict';
    // find the node
    const walker = wrapWalker(varWalker,
        (node, vb) => {
            if (node.start > pos || node.end < pos) {
                return false;
            }
            if (nodeTest(node)) {
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

/**
 * Find the smallest node that contains the range from start to end.
 * Note that we can find the node at the postNode instead of preNode.
 * @param ast
 * @param start
 * @param end
 * @returns {*}
 */
function findSurroundingNode(ast, start, end) {
    'use strict';

    const walker = wrapWalker(varWalker,
        node => node.start <= start && end <= node.end,
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