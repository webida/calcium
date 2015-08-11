const myWalker = require('./util/myWalker');

function getTypeData(ast, Ĉ, start, end) {
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

exports.getTypeData = getTypeData;