/**
 * @file Implements return / escaping statements finder
 * @author sewon326.kim@samsung.com
 */

const walk = require('acorn/dist/walk');
import * as myWalker from './util/myWalker'

/**
 * auxiliary function for visitor's state change
 * @param node
 * @param st
 * @param nodeType
 * @return {*}
 */
function _stChange(node, st, nodeType) {
    const [fnNode, tryNode, outerTryNode] = st;
    switch (nodeType) {
        case 'FunctionDeclaration':
        case 'FunctionExpression':
        case 'ArrowFunctionExpression':
            return [node, undefined];
        case 'TryStatement':
            // remember outer tryNode
            return [fnNode, node, tryNode];
        case 'CatchClause':
            // use outer try as its tryNode
            return [fnNode, outerTryNode];
        case 'BlockStatement':
            if (st.outer) {
                // it's finally block
                return [fnNode, outerTryNode];
            }
            else {
                // it's try block
                return [fnNode, tryNode, outerTryNode];
            }
        default:
            return [fnNode, tryNode, outerTryNode];
    }
}

/**
 * Check whether given pos is on a function keyword
 * @param ast - AST of a program
 * @param pos - index position
 * @return {*} - function node or null
 */
export function onEscapingStatement(ast, pos) {
    'use strict';

    // find function node
    // st is the enclosing function
    const walker = myWalker.wrapWalker(walk.make({
            TryStatement: (node, st, c) => {
                c(node.block, st);
                // set flag after processing try block
                st.outer = true;
                if (node.handler) c(node.handler, st);
                if (node.finalizer) c(node.finalizer, st);
            },
            CatchClause: (node, st, c) => {
                c(node.body, st);
            }
        }, walk.base),
        // pre
        (node, st, nodeType) => {
            if (node.start > pos || node.end < pos) {
                return false;
            }

            // on a function keyword, 8 is the length of 'function'
            // or on return keyword, 6 is the length of 'return'
            // or on throw keyword, 5 is the length of 'throw'
            if (((nodeType === 'FunctionDeclaration' || nodeType === 'FunctionExpression')
                && (node.start <= pos && pos <= node.start + 8))
                ||
                (nodeType === 'ReturnStatement'
                && (node.start <= pos && pos <= node.start + 6))
                ||
                (nodeType === 'ThrowStatement'
                && (node.start <= pos && pos <= node.start + 5))) {
                // record the found node type
                st.type = node.type;
                throw st;
            }
            return true;
        },
        // post
        undefined,
        _stChange
    );

    try {
        walk.recursive(ast, [], walker);
    } catch (e) {
        if (e && e instanceof Array) {
            // found
            return e;
        } else {
            // other error
            throw e;
        }
    }
    // identifier not found
    return null;
}

/**
 * Given a node, find its escaping nodes
 *
 * @param nodePair - AST node of a function, possibly with no annotation
 * @return {*} - array of AST nodes
 */
function _getEscapingNodes(nodePair) {
    'use strict';
    const nodes = [];
    const [fnNode, tryNode] = nodePair;

    const walker = myWalker.wrapWalker(
        walk.make({
            TryStatement: (node, st, c) => {
                c(node.block, st);
                // set flag after processing try block
                st.outer = true;
                // visit those BlockStatement
                if (node.handler) c(node.handler, st);
                if (node.finalizer) c(node.finalizer, st);
            },
            ReturnStatement: (node) => {
                if (nodePair.type === 'ThrowStatement' && tryNode) return;
                nodes.push(node);
            },
            Function: () => {
                // not visit inner functions
            },
            ThrowStatement: (node, [f,t]) => {
                if ((nodePair.type === 'ThrowStatement' && tryNode === t)
                    || t === undefined) {
                    nodes.push(node);
                }
            },
            CatchClause: (node, st, c) => {
                c(node.body, st);
            }
        }, walk.base),
        undefined,
        undefined,
        _stChange);

    if (nodePair.type === 'ThrowStatement' && tryNode) {
        walk.recursive(tryNode.block, [undefined, tryNode], walker);
    } else {
        walk.recursive(fnNode.body, [fnNode, undefined], walker);
    }

    return nodes;
}

/**
 * Find return nodes corresponding to the position
 * if the pos is on a function keyword
 *
 * @param ast - AST node of a program, possibly with no annotation
 * @param pos - cursor position
 * @param includeKeyword - whether to include keyword range
 * @return {Array} - array of AST nodes of escaping statements
 */
export function findEscapingStatements(ast, pos, includeKeyword) {
    'use strict';

    const nodePair = onEscapingStatement(ast, pos);
    if (!nodePair) {
        return null;
    }

    const ranges = _getEscapingNodes(nodePair).map(
            node => {
                return {start: node.start, end: node.end};
            });
    const [fnNode, tryNode] = nodePair;
    // If no explicit escaping exists
    // highlight the closing brace of the function body
    if (nodePair.type !== 'ThrowStatement' && ranges.length === 0) {
        ranges.push({start: fnNode.end - 1, end: fnNode.end});
    }

    // highlighting 'catch'
    if (nodePair.type === 'ThrowStatement' && tryNode) {
        ranges.push({start: tryNode.handler.start, end: tryNode.handler.start + 5});
    } else if (includeKeyword) {
        if (fnNode.type !== 'ArrowFunctionExpression') {
            // add ranges for 'function'
            ranges.push({start: fnNode.start, end: fnNode.start + 8});
        } else {
            // TODO: add range for fat arrow
        }
    }
    return ranges;
}
