var util = require('util');

function getNodeList(ast, startNum) {
    var nodeList = [];
    
    var num = startNum == undefined ? 0 : startNum;
    
    function assignId(node) {
        node['@label'] = num;
        nodeList.push(node);
        num++;
    }

    // Label every AST node with property 'type'
    function labelNodeWithType(node) {
        if (node && node.hasOwnProperty('type')) {
            assignId(node);
        }
        if (node && typeof node === 'object') {
            for (var p in node) {
                labelNodeWithType(node[p]);
            }
        }
    }
    
    labelNodeWithType(ast);
    
    return nodeList; 
}

function showUnfolded(obj) {
    console.log(util.inspect(obj, {depth: null}));
}

exports.getNodeList = getNodeList;
exports.showUnfolded = showUnfolded;
