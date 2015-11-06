const walk = require('acorn/dist/walk');

/**
 * Returns a walker that does nothing for each node.
 * Use as a base walker when you need to walk on only some types of nodes.
 * @returns {Object}
 */
function makeNoopWalker() {
    const walker = Object.create(null);
    const noopFunc = () => {};
    for (let name in Object.getOwnPropertyNames(walk.base)) {
        walker[name] = noopFunc;
    }
    return walker;
}
export const noopWalker = makeNoopWalker();

/**
 * Check whether the pattern uses defaults
 * @param ptnNode - a pattern node
 * @returns {boolean}
 */
export function patternHasDefaults(ptnNode) {
    const assignmentPatternFinder = walk.make(noopWalker, {
        AssignmentPattern: (node, st, c) => {
            throw new Found();
        },
        ObjectPattern: walk.base.ObjectPattern,
        ArrayPattern: walk.base.ArrayExpression,
        RestElement: walk.base.RestElement
    });

    try {
        walk.recursive(ptnNode, undefined, assignmentPatternFinder);
    } catch (e) {
        if (e instanceof Found) {
            return true;
        }
    }
    return false;
}

/**
 * a walker that visits each id even though it is var declaration
 * the parameter vb denote varBlock
 */
export const varWalker = walk.make({
    Function: (node, vb, c) => {
        if (node.id) c(node.id, vb, 'Pattern');
        const paramVb = node['@block'] || node.body['@block'];
        for (let i = 0; i < node.params.length; i++) {
            c(node.params[i], paramVb, 'Pattern');
        }
        const innerVb = node.body['@block'];
        c(node.body, innerVb, node.expression ? 'ScopeExpression' : 'ScopeBody');
    },
    ForStatement: (node, vb, c) => {
        const innerVb = node['@block'] || vb;
        // Use ForStatement of base walker
        walk.base.ForStatement(node, innerVb, c);
    },
    BlockStatement: (node, vb, c) => {
        const innerVb = node['@block'] || vb;
        // Use BlockStatement of base walker
        walk.base.BlockStatement(node, innerVb, c);
    },
    TryStatement: (node, vb, c) => {
        c(node.block, vb);
        if (node.handler) {
            // Do not visit parameter with current vb
            // the parameter will be visited in CatchClause with changed vb
            c(node.handler, vb);
        }
        if (node.finalizer) {
            c(node.finalizer, vb);
        }
    },
    CatchClause: (node, vb, c) => {
        const catchVb = node.body['@block'];
        // Need to handle the parameter in changed block
        c(node.param, catchVb);
        c(node.body, catchVb);
    },
    VariablePattern: (node, vb, c) => {
        // Note that walk.base.Identifier is 'ignore.'
        // varWalker should visit variables in LHS.
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
export function wrapWalker(walker, preNode, postNode, stChange) {
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
                newSt = stChange(node, st, nodeType);
            }
            if (!preNode || preNode(node, newSt, nodeType)) {
                ret = walker[nodeType](node, newSt, c);
            } else {
                return;
            }
            if (postNode) {
                ret = postNode(node, newSt, nodeType);
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
export class Found {
    constructor(info) {
        this.info = info;
    }
}

export function isDummyIdNode(node) {
    if (node.type !== 'Identifier') {
        throw new Error('Should be an Identifier node');
    }
    return node.name === '✖' && node.start >= node.end;
}

export function findIdentifierAt(ast, pos) {
    'use strict';
    return findNodeAt(ast, pos,
            node => node.type === 'Identifier' && !isDummyIdNode(node)
    );
}

export function findMemberOrVariableAt(ast, pos) {
    'use strict';
    return findNodeAt(ast, pos,
            node => {
                return (node.type === 'Identifier' && !isDummyIdNode(node)) ||
                    (node.type === 'MemberExpression' &&
                    (
                        (node.property.start <= pos && pos <= node.property.end) ||
                        // when prop is ✖
                        (node.property.end <= pos && pos <= node.property.start)
                    ));
            }
    );
}

export function findCompletionContext(ast, pos) {
    'use strict';
    // find the node
    const walker = wrapWalker(varWalker,
        (node, vb) => {
            if (node.start > pos || node.end < pos) {
                return false;
            }
            // at identifier?
            if (node.type === 'Identifier') {
                throw new Found({type: 'Identifier', node: node, vb: vb});
            }
            // at member expression?
            if (node.type === 'MemberExpression' &&
                (
                    (node.property.start <= pos && pos <= node.property.end) ||
                        // when prop is ✖
                    (node.property.end <= pos && pos <= node.property.start)
                )
            ) {
                // at usual prop? (after dot)
                if (!node.computed) {
                    throw new Found({type: 'usualProp', node: node, vb: vb});
                }
                // at obj[''] pattern?
                if (node.computed &&
                    typeof node.property.value === 'string') {
                    throw new Found({type: 'stringProp', node: node, vb: vb});
                }
            }
            return true;
        },
        (node, vb) => {
            // no Identifier or Member Expression was found
            throw new Found({type: 'Identifier', node: null, vb: vb});
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
export function findSurroundingNode(ast, start, end) {
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

export function recursiveWithReturn(node, state, visitor) {
    function c(node, st, override) {
        return visitor[override || node.type](node, st, c);
    }
    return c(node, state);
}
