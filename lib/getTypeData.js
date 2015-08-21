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

function computeIconOfProp(propMap) {
    const iconMap = new Map();

    function isObject(icon) {
        return icon === 'object' || icon === 'array' || icon === 'fn';
    }

    propMap.forEach((tps, p) => {
        for (let tp of tps) {
            let icon;
            if (tp === types.PrimNumber) icon = 'number';
            else if (tp === types.PrimBoolean) icon = 'bool';
            else if (tp === types.PrimString) icon = 'string';
            else if (tp instanceof types.FnType) icon = 'fn';
            else if (tp instanceof types.ArrType) icon = 'array';
            else if (tp instanceof types.ObjType) icon = 'object';

            if (!iconMap.has(p) || iconMap.get(p) === icon) {
                iconMap.set(p, icon);
                continue;
            }

            if (isObject(icon) && isObject(iconMap.get(p))) {
                iconMap.set(p, 'object');
            } else {
                iconMap.set(p, 'unknown');
                break;
            }
        }
        console.info(p);
        if (tps.size === 0) {
            iconMap.set(p, 'unknown');
        }
    });
    return iconMap;
}

/**
 * Get prop to icon map from given node
 * @param Ĉ - AbsCache
 * @param node - expression node
 * @returns {Map.<string, string>} - Mapping from prop to icon
 */
export function getPropFromNode(Ĉ, node) {
    const nodeTypes = Ĉ.getTypeOfLoc(node);
    //console.info(getReadablePropMap(nodeTypes));
    const propMap = getReadablePropMap(nodeTypes);
    return computeIconOfProp(propMap);
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
                for (let [p, i] of props) {
                    list.push({text: p, icon: i});
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
                for (let [p, i] of props) {
                    if (p.startsWith(prefix)) {
                        list.push({text: p, icon: i});
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


function unionMap(m1, m2) {
    const ret = new Map();

    function unionSet(s1, s2) {
        const ret = new Set();
        if (s1) s1.forEach(e => ret.add(e));
        if (s2) s2.forEach(e => ret.add(e));
        return ret;
    }

    if (m1) m1.forEach((ts, p) => ret.set(p, ts));
    if (m2) m2.forEach((ts, p) => ret.set(p, unionSet(ret.get(p), m2.get(p))));
    return ret;
}

function addOnlyMissingProps(m1, m2) {
    const ret = new Map();
    m1.forEach((ts, p) => ret.set(p, ts));
    m2.forEach((ts, p) => {
        if (!ret.has(p)) ret.set(p, ts)
    });
    return ret;
}

function getReadablePropMap(tps) {

    const visitedTypes = [];

    function traverse(type) {
        if (type instanceof types.ObjType &&
            type.getProp('__proto__', true)) {
            let protoMap = new Map();
            const protoTypes = type.getProp('__proto__', true).getTypes();

            protoTypes.forEach(tp => {
                if (visitedTypes.indexOf(tp) > -1) {
                    return;
                }
                visitedTypes.push(tp);
                protoMap = unionMap(protoMap, traverse(tp));
                visitedTypes.pop();
            });
            const retMap = new Map();
            type.props.forEach((av, p) => {
                retMap.set(p, av.getTypes());
            });
            return addOnlyMissingProps(retMap, protoMap);
        } else {
            return new Map();
        }
    }

    let retMap = new Map();
    tps.forEach(tp => {
        retMap = unionMap(retMap, traverse(tp))
    });

    return retMap;
}
