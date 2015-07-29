/**
 * Wrap a walker with pre- and post- actions
 *
 * @param preNode - Apply before visiting the current node.
 * If returns false, do not visit the node.
 * @param postNode - Apply after visiting the current node.
 * If given, return values are overridden.
 * @returns {*} - a new walker
 */
function wrapWalker(walker, preNode, postNode) {
    const retWalker = {};
    // wrapping each function preNode and postNode
    for (let nodeType in walker) {
        if (!walker.hasOwnProperty(nodeType)) {
            continue;
        }
        retWalker[nodeType] = (node, st, c) => {
            let ret;
            if (!preNode || preNode(node, st, c)) {
                ret = walker[nodeType](node, st, c);
            } else {
                return;
            }
            if (postNode) {
                ret = postNode(node, st, c);
            }
            return ret;
        }
    }
    return retWalker;
}

exports.wrapWalker = wrapWalker;