import * as myWalker from './util/myWalker'
import * as types from './domains/types'

/**
 * Get types of expression at the given range
 * @param ast
 * @param Ĉ
 * @param start
 * @param end
 * @returns {{hasType: boolean, typeString: string, nodeStart: number, nodeEnd: number}}
 */
export function getTypeAtRange(ast, Ĉ, start, end) {
    'use strict';
    const node = myWalker.findSurroundingNode(ast, start, end);
    const nodeTypes = Ĉ.getTypeOfLoc(node);
    let hasType;
    let typeString = '';
    if (!nodeTypes) {
        hasType = false;
        typeString = 'No expression at the given range';
    } else {
        hasType = true;
        typeString = '';
        nodeTypes.forEach(function (tp, i) {
            typeString += tp.getName();
            if (i !== nodeTypes.length - 1) {
                typeString += ', ';
            }
        });
    }
    return {
        hasType: hasType,
        typeString: typeString,
        nodeStart: node.start,
        nodeEnd: node.end
    };
}

/**
 * Get possible properties of given node
 * @param Ĉ - AbsCache
 * @param node - expression node
 * @returns {Set} - set of property names
 */
export function getPropFromNode(Ĉ, node) {
    const nodeTypes = Ĉ.getTypeOfLoc(node);
    if (!nodeTypes) {
        // node does not have types
        return null;
    }

    const foundTypes = [];

    function addFoundType(tp) {
        if (foundTypes.indexOf(tp) > -1) {
            return false;
        } else {
            foundTypes.push(tp);
            return true;
        }
    }

    // Initialization
    nodeTypes.forEach(addFoundType);

    // Add types recursively in the prototype chains
    for (let i = 0; i !== foundTypes.length; i++) {
        let foundType = foundTypes[i];
        if (foundType instanceof types.ObjType) {
            let protoAVal = foundType.getProp('__proto__', true);
            if (protoAVal) {
                protoAVal.getTypes().forEach(addFoundType);
            }
        }
    }

    // Find all properties from foundTypes
    const propNames = new Set();
    foundTypes.forEach(tp => {
        if (tp instanceof types.ObjType) {
            for (let name of tp.getOwnPropNames()) {
                if (!propNames.has(name)) {
                    propNames.add(name);
                }
            }
        }
    });

    return propNames;
}

/**
 * For debugging, show x
 * @param x
 */
function SHOW(x) {
    console.info(x);
    return x;
}

export function getCompletionAtPos(result, pos) {
    // find id or member node
    const nodeInfo = myWalker.findMemberOrVariableAt(result.AST, pos);

    if (nodeInfo) {
        // some node is found
        console.info('found node:', nodeInfo.node);
        if (nodeInfo.node.type === 'MemberExpression') {
            const objectNode = nodeInfo.node.object;
            const propertyNode = nodeInfo.node.property;
            const props = getPropFromNode(result.Ĉ, objectNode);
            const propName = propertyNode.name;

            if (propName === '✖') {
                // ✖ is inserted prop for error recovery
                const list = [];
                for (let p of props.values()) {
                    list.push(p);
                }
                return SHOW({
                    list: list,
                    // Here, end is correct for start position
                    from: propertyNode.end,
                    to: pos
                });
            } else {
                const prefix = propName.substr(0, pos - propertyNode.start);
                const list = [];
                for (let p of props.values()) {
                    if (p.startsWith(prefix)) {
                        list.push(p);
                    }
                }
                return SHOW({
                    list: list,
                    from: propertyNode.start,
                    to: pos
                });
            }
        }
        if (nodeInfo.node.type === 'Identifier') {
            const varNode = nodeInfo.node;
            const varName = varNode.name;
            const currBlock = nodeInfo.vb;
            const varNames = currBlock.getVarNamesInChain();

            if (varName === '✖') {
                return SHOW({
                    list: varNames,
                    // Here, we should use end for start position
                    from: varNode.end,
                    to: pos
                });
            } else {
                const prefix = varName.substr(0, pos - varNode.start);
                const list = varNames.filter(p => p.startsWith(prefix));
                return SHOW({
                    list: list,
                    from: nodeInfo.node.start,
                    to: pos
                });
            }
        }
    }
    return null;
}