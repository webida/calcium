/**
 * @file Implements variable occurrence finder.
 * @author sewon326.kim@samsung.com
 */

const walk = require('acorn/dist/walk');
import * as myWalker from './util/myWalker'

/**
 * Finds occurrences of the variable at `pos`.
 * @param ast - scope annotated AST
 * @param {number} pos - character position
 * @return {*} - array of AST nodes
 */
export function findVarRefsAt(ast, pos) {
    'use strict';
    const found = myWalker.findIdentifierAt(ast, pos);
    if (!found) {
        // pos is not at a variable
        return null;
    }
    // find refs for the id node
    const refs = _findRefsToVariable(found).map(node =>
        ({start: node.start, end: node.end})
    );
    refs.varName = found.node.name;

    return refs;
}

/**
 * @param found - node and varBlock of the variable
 * @return {Array} - array of AST nodes
 */
function _findRefsToVariable(found) {
    'use strict';
    const varName = found.node.name;
    const vb1 = found.vb.findVarInChain(varName);
    if (!vb1) return [];

    const refs = [];

    const walker = walk.make({
        Identifier: (node, vb) => {
            if (node.name !== varName) return;
            if (vb1 === vb.findVarInChain(varName)) {
                refs.push(node);
            }
        }
    }, myWalker.varWalker);

    walk.recursive(vb1.originNode, vb1.originNode['@block'], walker);
    return refs;
}
