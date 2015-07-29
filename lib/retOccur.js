const walk = require('acorn/dist/walk');
const myWalker = require('./util/myWalker');

/**
 * Check whether given pos is on a function keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @returns {*} - function node or null
 */
function onFunctionKeyword(ast, pos) {
    "use strict";

    // find function node
    const walker = myWalker.wrapWalker(walk.base,
        (node, vb) => {
            if (node.start > pos || node.end < pos) {
                return false;
            }
            // 8 is the length of 'function' keyword
            if ((node.type === 'FunctionDeclaration'
                || node.type === 'FunctionExpression')
                && (node.start <= pos && pos <= node.start + 8)) {
                throw node;
            }
            return true;
        });

    try {
        walk.recursive(ast, undefined, walker);
    } catch (e) {
        if (e && e.type &&
            (e.type === 'FunctionExpression'
            || e.type === 'FunctionDeclaration')) {
            return e;
        } else {
            throw e;
        }
    }
    // identifier not found
    return null;
}

/**
 * Given a function node, find its return nodes
 *
 * @param fNode - AST node of a function, possibly with no annotation
 * @returns {*} - array of AST nodes
 */
function getReturnNodes(fNode) {
    "use strict";
    const rets = [];
    if (fNode.type !== 'FunctionExpression'
        && fNode.type !== 'FunctionDeclaration') {
        throw Error('fNode should be a function node');
    }

    const walker = walk.make({
        ReturnStatement: (node) => {
            return rets.push(node);
        },
        Function: () => {
            // not visit inner functions
        }
    }, walk.base);

    walk.recursive(fNode.body, undefined, walker);

    return rets;
}

/**
 * Find return nodes corresponding to the position
 * if the pos is on a function keyword
 *
 * @param ast - AST node of a program, possibly with no annotation
 * @param pos - cursor position
 * @param includeFunctionKeyword - whether to include function keyword range
 * @returns {Array} - array of AST nodes of return statements
 */
function findReturnStatements(ast, pos, includeFunctionKeyword) {
    "use strict";

    const fNode = onFunctionKeyword(ast, pos);
    if (!fNode) {
        // pos is not on function keyword
        return null;
    }

    const refs = getReturnNodes(fNode);
    if (includeFunctionKeyword) {
        refs.push({start: fNode.start, end: fNode.start + 8});
    }
    return refs;
}

exports.onFunctionKeyword = onFunctionKeyword;
exports.findReturnStatements = findReturnStatements;