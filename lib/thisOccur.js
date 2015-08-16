const walk = require('acorn/dist/walk');
const myWalker = require('./util/myWalker');

/**
 * Check whether given pos is on a this keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @returns {*} - function node or null
 */
function onThisKeyword(ast, pos) {
    'use strict';

    // find function node
    // st is the enclosing function
    const walker = myWalker.wrapWalker(walk.base,
        // pre
        (node, st) => {
            if (node.start > pos || node.end < pos) {
                return false;
            }

            if (node.type === 'ThisExpression') {
                throw st;
            }
            return true;
        },
        // post
        undefined,
        // stChange
        (node, st) => {
            if (node.type === 'FunctionDeclaration'
                || node.type === 'FunctionExpression') {
                return node;
            } else {
                return st;
            }
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
 * Given a function node, find its this nodes
 *
 * @param fNode - AST node of a function, possibly with no annotation
 * @returns {*} - array of AST nodes
 */
function getThisNodes(fNode) {
    'use strict';
    const rets = [];
    if (fNode.type !== 'FunctionExpression'
        && fNode.type !== 'FunctionDeclaration') {
        throw Error('fNode should be a function node');
    }

    const walker = walk.make({
        ThisExpression: (node) => {
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
 * Find this nodes if the pos is on a this keyword
 *
 * @param ast - AST node of a program, possibly with no annotation
 * @param pos - cursor position
 * @param includeFunctionKeyword - whether to include function keyword range
 * @returns {Array} - array of AST nodes of return statements
 */
function findThisExpressions(ast, pos, includeFunctionKeyword) {
    'use strict';

    const fNode = onThisKeyword(ast, pos);
    if (!fNode) {
        // pos is not on this keyword
        return null;
    }

    const rets = getThisNodes(fNode);
    if (includeFunctionKeyword) {
        rets.push({start: fNode.start, end: fNode.start + 8});
    }
    return rets;
}

exports.onThisKeyword = onThisKeyword;
exports.findThisExpressions = findThisExpressions;