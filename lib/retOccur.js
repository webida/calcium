const walk = require('acorn/dist/walk');
import * as myWalker from './util/myWalker'

/**
 * auxiliary function for visitor's state change
 * @param node
 * @param st
 * @param nodeType
 * @returns {*}
 */
function stChange(node, st, nodeType) {
    const [fnNode, tryNode, outerTryNode] = st;
    switch (nodeType) {
        case 'FunctionDeclaration':
        case 'FunctionExpression':
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
 * @returns {*} - function node or null
 */
function onEscapingStatement(ast, pos) {
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
        // stChange
        stChange
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
 * @returns {*} - array of AST nodes
 */
function getEscapingNodes(nodePair) {
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
        stChange);

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
 * @returns {Array} - array of AST nodes of escaping statements
 */
function findEscapingStatements(ast, pos, includeKeyword) {
    'use strict';

    const nodePair = onEscapingStatement(ast, pos);
    if (!nodePair) {
        return null;
    }

    const nodes = getEscapingNodes(nodePair);
    const [fnNode, tryNode] = nodePair;
    // If no explicit escaping exists
    // highlight the closing brace of the function body
    if (nodePair.type !== 'ThrowStatement' && nodes.length === 0) {
        nodes.push({start: fnNode.end - 1, end: fnNode.end});
    }

    // highlighting 'catch'
    if (nodePair.type === 'ThrowStatement' && tryNode) {
        nodes.push({start: tryNode.handler.start, end: tryNode.handler.start + 5});
    } else if (includeKeyword) {
        // highlighting 'function'
        nodes.push({start: fnNode.start, end: fnNode.start + 8});
    }
    return nodes;
}

exports.onEscapingStatement = onEscapingStatement;
exports.findEscapingStatements = findEscapingStatements;
