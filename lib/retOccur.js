const walk = require('acorn/dist/walk');
const myWalker = require('./util/myWalker');

/**
 * Check whether given pos is on a function keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @returns {*} - function node or null
 */
function onFunctionOrReturnKeyword(ast, pos) {
    'use strict';

    // find function node
    // st is the enclosing function
    const walker = myWalker.wrapWalker(walk.base,
        // pre
        (node, st) => {
            if (node.start > pos || node.end < pos) {
                return false;
            }

            // on a function keyword, 8 is the length of 'function'
            // or on return keyword, 6 is the length of 'return'
            if (((node.type === 'FunctionDeclaration' || node.type === 'FunctionExpression')
                && (node.start <= pos && pos <= node.start + 8))
                ||
                (node.type === 'ReturnStatement'
                && (node.start <= pos && pos <= node.start + 6))) {
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
 * Given a function node, find its return nodes
 *
 * @param fNode - AST node of a function, possibly with no annotation
 * @returns {*} - array of AST nodes
 */
function getReturnNodes(fNode) {
    'use strict';
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
    'use strict';

    const fNode = onFunctionOrReturnKeyword(ast, pos);
    if (!fNode) {
        // pos is not on function keyword
        return null;
    }

    const rets = getReturnNodes(fNode);
    // when function does not have return statements,
    // indicate it by the closing brace of the function body
    if (rets.length === 0) {
        rets.push({start: fNode.end - 1, end: fNode.end});
    }
    if (includeFunctionKeyword) {
        rets.push({start: fNode.start, end: fNode.start + 8});
    }
    return rets;
}

exports.onFunctionOrReturnKeyword = onFunctionOrReturnKeyword;
exports.findReturnStatements = findReturnStatements;