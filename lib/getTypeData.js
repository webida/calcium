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
    const nodeTypes = Ĉ.getMergedAValOfLoc(node);
    let hasType;
    let typeString = '';
    if (!nodeTypes) {
        hasType = false;
        typeString = 'No types at the given range';
    } else {
        hasType = true;
        typeString = nodeTypes.toString();
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
    // Since getTypeOfLoc can return null if node does not have any types
    const nodeTypes = Ĉ.getMergedAValOfLoc(node);
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
    const nodeInfo = myWalker.findCompletionContext(result.AST, pos);

    if (nodeInfo.type === 'Identifier') {
        let prefix, from, to;

        if (nodeInfo.node === null) {
            prefix = '';
            from = pos;
            to = pos;
        } else if (myWalker.isDummyIdNode(nodeInfo.node)) {
            prefix = '';
            from = to = nodeInfo.node.end; // Here, end is correct for start position
        } else {
            prefix = nodeInfo.node.name;
            from = nodeInfo.node.start;
            to = nodeInfo.node.end;
        }
        const varMap = computeIconOfProp(getReadableVarMap(nodeInfo.vb));

        const list = [];
        for (let [v, i] of varMap) {
            if (v.startsWith(prefix)) {
                list.push({text: v, icon: i});
            }
        }
        return SHOW({list: list, from: from, to: to});

    } else {
        // property completion
        const objectNode = nodeInfo.node.object;
        const props = getPropFromNode(result.Ĉ, objectNode);

        const propertyNode = nodeInfo.node.property;
        let prefix, from, to, filter;
        if (nodeInfo.type === 'usualProp') {
            const propName = propertyNode.name;
            if (myWalker.isDummyIdNode(propertyNode)) {
                prefix = '';
                from = propertyNode.end; // Here, end is correct for start position
            } else {
                // prefix = propName.substr(0, pos - propertyNode.start);
                prefix = propName;
                from = propertyNode.start;
            }
            to = propertyNode.end;
            filter = p => (/^[$A-Z_][0-9A-Z_$]*$/i).test(p);
        } else if (nodeInfo.type === 'stringProp') {
            prefix = propertyNode.value;
            from = propertyNode.start + 1;
            to = propertyNode.end - 1;
            filter = p => true
        }

        const list = [];
        for (let [p, i] of props) {
            // unknown prop is null
            if (p !== null && p.startsWith(prefix) && filter(p)) {
                list.push({text: p, icon: i});
            }
        }
        return SHOW({list: list, from: from, to: to});
    }
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

function addOnlyMissingMappings(m1, m2) {
    const ret = new Map();
    m1.forEach((ts, p) => ret.set(p, ts));
    m2.forEach((ts, p) => {
        if (!ret.has(p)) ret.set(p, ts)
    });
    return ret;
}

// convert a map of A -> AVal
// to a map of A -> Set.<Type>
function convertMap(map) {
    let retMap = new Map();
    map.forEach((av, p) => {
        retMap.set(p, av.getTypes());
    });
    return retMap;
}

// traverse abstract heap space
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
            return addOnlyMissingMappings(convertMap(type.props), protoMap);
        } else {
            return new Map();
        }
    }

    let retMap = new Map();
    tps.getTypes().forEach(tp => {
        retMap = unionMap(retMap, traverse(tp))
    });

    return retMap;
}

// traverse abstract stack space
function getReadableVarMap(vb) {
    let currVB = vb;
    let retMap = new Map();
    while (currVB !== null) {
        let mergedMap = new Map();
        for (let varMap of currVB.instances.values()) {
            mergedMap = unionMap(mergedMap, convertMap(varMap));
        }
        retMap = addOnlyMissingMappings(retMap, mergedMap);
        currVB = currVB.paren;
    }
    return retMap;
}
