/**
 * @file Implements VarBlock and Scope
 * @author sewon326.kim@samsung.com
 */

'use strict';

import * as types from './domains/types'
import * as myWalker from './util/myWalker'
const walk = require('acorn/dist/walk');

export class VarBlock {
    /**
     * Constructs a VarBlock.
     * @param {VarBlock} paren
     * @param originNode
     * @param bType
     * @param {boolean} isStrict
     */
    constructor(paren, originNode, bType, isStrict) {
        this.paren = paren;
        this.originNode = originNode;
        this.blockType = bType;
        this.isStrict = isStrict;

        this.originLabel = originNode['@label'];
        this.paramVarNames = [];
        this.localVarNames = [];

        this.usedVariables = [];
        // this.useArgumentsObject
        this.instances = new Map();
        this.scopeInstances = [];
    }

    /**
     * Checks whether it is a global block.
     * @return {boolean}
     */
    isGlobal() {
        return this.blockType === VarBlock.blockTypes.globalBlock;
    }

    /**
     * Checks whether it is an ES5 function block.
     * @return {boolean}
     */
    isOldFunctionBlock() {
        return this.blockType === VarBlock.blockTypes.oldFunctionBlock;
    }

    /**
     * Checks whether it is a block of an arrow function.
     * @return {boolean}
     */
    isArrowFunctionBlock() {
        return this.blockType === VarBlock.blockTypes.arrowFunctionBlock;
    }

    /**
     * Checks whether it is a catch block.
     * @return {boolean}
     */
    isCatchBlock() {
        return this.blockType === VarBlock.blockTypes.catchBlock;
    }

    /** Checks whether is is a normal code block.
     * @return {boolean}
     */
    isNormalBlock() {
        return this.blockType === VarBlock.blockTypes.normalBlock;
    }

    /**
     * Checks whether it is a parameter block.
     * @return {boolean}
     */
    isParameterBlock() {
        return this.blockType === VarBlock.blockTypes.parameterBlock;
    }

    /**
     * Returns the names of local variables.
     * @return {Array.<string>}
     */
    getLocalVarNames() {
        return this.localVarNames;
    }

    /**
     * Returns the names of parameters.
     * @return {Array.<string>}
     */
    getParamVarNames() {
        return this.paramVarNames;
    }

    /**
     * Returns the names of its parameter and local variables.
     * @return {Array.<string>}
     */
    getVarNames() {
        return this.getLocalVarNames().concat(this.getParamVarNames());
    }

    /**
     * Checks whether it has a local variable whose name is `varName`.
     * @param {string} varName
     * @return {boolean}
     */
    hasLocalVar(varName) {
        return this.localVarNames && this.localVarNames.indexOf(varName) > -1;
    }

    /**
     * Checks whether it has a parameter varialbe whose name is `varName`.
     * @param {string} varName
     * @return {boolean}
     */
    hasParamVar(varName) {
        return this.paramVarNames.indexOf(varName) > -1;
    }

    /**
     * Checks whether the block has variable named as `varName`.
     * @param {string} varName
     * @return {boolean}
     */
    hasVar(varName) {
        return this.hasParamVar(varName) || this.hasLocalVar(varName);
    }

    /**
     * Add a declared variable to the block.
     * It returns null if it does not add the variable.
     * @param {string} varName
     * @param dType - declaration type
     * @return {VarBlock|null}
     */
    addDeclaredLocalVar(varName, dType) {
        let currBlock = this;
        switch(dType) {
            case VarBlock.declarationTypes.varDeclaration:
                // Go up until function or global
                while (!currBlock.isOldFunctionBlock()
                    && !currBlock.isArrowFunctionBlock()
                    && !currBlock.isParameterBlock()  // to add 'arguments'
                    && !currBlock.isGlobal()) {
                    currBlock = currBlock.paren;
                }
                break;
            case VarBlock.declarationTypes.functionDeclaration:
                // Go up until function or global
                // or catch block having varName as its parameter
                while (currBlock.isNormalBlock() &&
                       !(currBlock.isCatchBlock() && currBlock.hasParamVar(varName))) {
                    currBlock = currBlock.paren;
                }
                break;
            case VarBlock.declarationTypes.letDeclaration:
            case VarBlock.declarationTypes.constDeclaration:
                break;
            case VarBlock.declarationTypes.implicitGlobalDeclaration:
                // not global or strict => do not add the variable
                if (!this.isGlobal() || this.isStrict) {
                    return null;
                }
                break;
        }

        // if already added, do not add
        if (!currBlock.hasVar(varName)) {
            currBlock.localVarNames.push(varName);
        }
        // returns the block object that contains the variable
        return currBlock;
    }

    /**
     * Adds a parameter variable.
     * @param {string} varName
     */
    addParamVar(varName) {
        this.paramVarNames.push(varName);
    }

    /**
     * Returns the VarBlock that contains `varName`.
     * It can recursively look into `paren` VarBlocks.
     * @param varName
     * @return {VarBlock}
     */
    findVarInChain(varName) {
        let currBlock = this;
        while (currBlock && !currBlock.hasVar(varName)) {
            if (currBlock.isGlobal() && !currBlock.isStrict) {
                break;
            }
            currBlock = currBlock.paren;
        }
        // if not found
        // 1) global 'use strict' => returns null
        // 2) otherwise => returns the global
        return currBlock;
    }

    /**
     * Get all the variable names in the chain of VarBlock.
     * @return {Array.<string>}
     */
    getVarNamesInChain() {
        let currBlock = this;
        const varNames = [];
        while (currBlock) {
            currBlock.getVarNames().forEach(function (name) {
                if (varNames.indexOf(name) === -1) {
                    varNames.push(name);
                }
            });
            currBlock = currBlock.paren;
        }
        return varNames;
    }

    /**
     * Add `varName` as one of the used variables.
     * @param {string} varName
     */
    addUsedVar(varName) {
        if (this.usedVariables.indexOf(varName) === -1) {
            this.usedVariables.push(varName);
        }
    }

    /**
     * Returns the used variables.
     * @return {Array.<string>}
     */
    getUsedVarNames() {
        return this.usedVariables;
    }

    /**
     * Checks whether `varName` is used.
     * @param varName
     * @return {boolean}
     */
    isUsedVar(varName) {
        return this.usedVariables.indexOf(varName) > -1;
    }

    /**
     * Returns a mapping from variable names to their AVals.
     * @param {CallSiteContext} delta
     * @return {Map.<string, AVal>}
     */
    getInstance(delta) {
        if (this.instances.has(delta)) {
            return this.instances.get(delta);
        }
        // construct VarMap
        const varMap = new Map();
        const varNames = this.getParamVarNames().concat(this.getLocalVarNames());

        for (let i = 0; i < varNames.length; i++) {
            varMap.set(varNames[i], new types.AVal());
        }
        // remember the instance
        this.instances.set(delta,varMap);
        return varMap;
    }

    /**
     * Returns an array of AVals for parameters
     * @param delta
     * @returns {Array.<AVal>}
     */
    getParamAVals(delta) {
        const instance = this.getInstance(delta);
        const params = [];
        this.getParamVarNames().forEach(name => {
            params.push(instance.get(name));
        });
        return params;
    }

    /**
     * Returns an AVal for `arguments`.
     * @param delta
     * @returns {AVal}
     */
    getArgumentsAVal(delta) {
        if (!this.useArgumentsObject) {
            throw new Error('Not for this VarBlock');
        }
        return this.getInstance(delta).get('arguments');
    }

    /**
     * Get a Scope instance
     * @param paren
     * @param delta
     * @returns {*}
     */
    getScopeInstance(paren, delta) {
        const varMap = this.getInstance(delta);
        let found = null;

        this.scopeInstances.forEach(function (sc) {
            if (sc.paren === paren && sc.varMap === varMap) found = sc;
        });

        if (found) {
            return found;
        } else {
            let newScopeInstance = new Scope(paren, varMap, this);
            this.scopeInstances.push(newScopeInstance);
            return newScopeInstance;
        }
    }

    /**
     * Get function's scope instances whose paren is `pScope`.
     * @param pScope
     * @returns {Set.<Scope>}
     */
    getScopesWithParent(pScope) {
        const instances = new Set();
        this.scopeInstances.forEach(sc => {
            if (sc.paren === pScope) instances.add(sc);
        });
        return instances;
    }
}

/**
 * @static
 */
VarBlock.blockTypes = {
    globalBlock: Symbol('global'),
    oldFunctionBlock: Symbol('oldFunction'),
    arrowFunctionBlock: Symbol('arrowFunction'),
    parameterBlock: Symbol('parameter'),  // though not really in braces
    catchBlock: Symbol('catch'),
    normalBlock: Symbol('normal')
};

/**
 * @static
 */
VarBlock.declarationTypes = {
    letDeclaration: Symbol('let'),
    constDeclaration: Symbol('const'),
    varDeclaration: Symbol('var'),
    functionDeclaration: Symbol('function'),
    parameterDeclaration: Symbol('parameter'),
    implicitGlobalDeclaration: Symbol('implicit global')
};

/**
 * Check whether the stmt is the directive for strictness.
 * Taken from acorn
 * @param stmt - the first statement of a body
 * @return {boolean}
 */
function _isUseStrict(stmt) {
    return stmt.type === 'ExpressionStatement' &&
        stmt.expression.type === 'Literal' &&
        stmt.expression.raw.slice(1, -1) === 'use strict';
}


const _declaredVariableFinder = walk.make({
    VariablePattern: (node, [dType, currBlock], c) => {
        if (dType === VarBlock.declarationTypes.parameterDeclaration) {
            currBlock.addParamVar(node.name);
        } else if (dType) {
            currBlock.addDeclaredLocalVar(node.name, dType);
        }
    },
    Function: (node, [dType, currBlock], c) => {
        let parenBlock = currBlock, paramBlock;
        if (node.id) {
            const funcName = node.id.name;
            parenBlock = currBlock.addDeclaredLocalVar(funcName,
                VarBlock.declarationTypes.functionDeclaration);
        }
        const hasParamScope = node.params.some((ptn) =>
            myWalker.patternHasDefaults(ptn));
        if (hasParamScope) {
            paramBlock = parenBlock = new VarBlock(
                parenBlock,
                node,
                VarBlock.blockTypes.parameterBlock,
                currBlock.isStrict
            );
            node['@block'] = paramBlock;
        }
        const strictInner = currBlock.isStrict ||
            (node.body.body &&
             node.body.body[0] &&
             _isUseStrict(node.body.body[0]));
        const funcBlock = new VarBlock(
            parenBlock,
            node,  // same originNode with paramBlock, intended.
            node.type === 'ArrowFunctionExpression'?
                VarBlock.blockTypes.arrowFunctionBlock
                : VarBlock.blockTypes.oldFunctionBlock,
            strictInner
        );
        funcBlock.hasParamScope = hasParamScope;
        node.body['@block'] = funcBlock;

        // add function parameters to corresponding scope
        const paramTargetBlock = paramBlock || funcBlock;
        for (let i = 0; i < node.params.length; i++) {
            c(node.params[i],
                [
                    VarBlock.declarationTypes.parameterDeclaration,
                    paramTargetBlock
                ],
                'Pattern');
        }

        if (node.expression) {
            c(node.body, [, funcBlock], 'Expression');
        } else {
            walk.base.BlockStatement(node.body, [, funcBlock], c);
        }
    },

    ForStatement: (node, [, currBlock], c) => {
        let forBlock;
        if (currBlock.isStrict) {
            forBlock = new VarBlock(
                currBlock,
                node,
                VarBlock.blockTypes.normalBlock,
                currBlock.isStrict
            );
            node['@block'] = forBlock;
        } else {
            forBlock = currBlock;
        }
        if (node.init) c(node.init, [, forBlock], 'ForInit');
        if (node.test) c(node.test, [, forBlock], 'Expression');
        if (node.update) c(node.update, [, forBlock], 'Expression');
        // its body can have a separate block.
        c(node.body, [, forBlock], undefined);
    },

    VariableDeclaration: (node, [, currBlock], c) => {
        let dType;
        switch(node.kind) {
            case 'var':
                dType = VarBlock.declarationTypes.varDeclaration;
                break;
            case 'let':
                dType = VarBlock.declarationTypes.letDeclaration;
                break;
            case 'const':
                dType = VarBlock.declarationTypes.constDeclaration;
                break;
        }

        for (let i = 0; i < node.declarations.length; i++) {
            c(node.declarations[i], [dType, currBlock], undefined);
        }
    },

    TryStatement: (node, [, currScope], c) => {
        c(node.block, [, currScope], undefined);
        if (node.handler) {
            c(node.handler, [, currScope], undefined);
        }
        if (node.finalizer) {
            c(node.finalizer, [, currScope], undefined);
        }
    },

    CatchClause: (node, [, currBlock], c) => {
        const catchBlock = new VarBlock(
            currBlock,
            node,
            VarBlock.blockTypes.catchBlock,
            currBlock.isStrict
        );
        c(node.param,
            [
                VarBlock.declarationTypes.parameterDeclaration,
                catchBlock
            ],
            'Pattern');
        node.body['@block'] = catchBlock;
        walk.base.BlockStatement(node.body, [, catchBlock], c);
    },

    // Create VarBlock of type normalBlock
    BlockStatement: (node, [, currBlock], c) => {
        let inBlock;
        if (currBlock.isStrict) {
            inBlock = new VarBlock(
                currBlock,
                node,
                VarBlock.blockTypes.normalBlock,
                currBlock.isStrict
            );
            node['@block'] = inBlock;
        } else {
            inBlock = currBlock;
        }
        walk.base.BlockStatement(node, [, inBlock], c);
    }
});

// For variables in global and arguments in functions
const _variableUsageCollector = walk.make({
    VariablePattern: (node, currBlock, c) => {
        c(node, currBlock, 'Identifier');
    },

    Identifier: (node, currBlock, c) => {
        if (myWalker.isDummyIdNode(node)) {
            // Skip dummy Id node
            return;
        }
        let block = currBlock;
        const varName = node.name;

        while (block && !block.hasVar(varName)) {
            if (varName === 'arguments' &&
                (block.isOldFunctionBlock() ||
                 block.isParameterBlock())) {
                if (block.hasParamScope) {
                    block = block.paren;
                    if (block.hasVar(varName)) break;
                }
                block.useArgumentsObject = true;
                // consider 'var' is used for declaration of 'arguments.'
                block.addDeclaredLocalVar(varName, VarBlock.declarationTypes.varDeclaration);
                break;
            }
            if (block.isGlobal()) {
                block.addDeclaredLocalVar(varName, VarBlock.declarationTypes.implicitGlobalDeclaration);
                break;
            }
            block = block.paren;
        }
        if (block.hasVar(varName)) {
            block.addUsedVar(varName);
        }
    },

    ReturnStatement: (node, currBlock, c) => {
        let block = currBlock;
        while (block.isCatchBlock() || block.isNormalBlock()) {
            block = block.paren;
        }
        if (!block.isGlobal() && node.argument !== null) {
            block.useReturnWithArgument = true;
        }
        if (node.argument) {
            c(node.argument, currBlock, undefined);
        }
    },

    Function: (node, currBlock, c) => {
        if (node.id) c(node.id, currBlock, 'Pattern');
        if (node['@block']) {
            const paramBlock = node['@block'];
            for (let i = 0; i < node.params.length; i++) {
                c(node.params[i], paramBlock, 'Pattern');
            }
        }
        c(node.body, currBlock);
    },

    ScopeBody: (node, currBlock, c) => {
        c(node, node['@block'] || currBlock);
    },

    BlockStatement: (node, currBlock, c) => {
        // Process BlockStatement with changed VarBlock
        walk.base.BlockStatement(node, node['@block'] || currBlock, c);
    }
});

/**
 * Analyzes `ast` and annotates it with VarBlocks.
 * @param ast
 * @param gVarBlock
 * @return {*}
 */
export function annotateBlockInfo(ast, gVarBlock) {
    ast['@block'] = gVarBlock;

    gVarBlock.isStrict = gVarBlock.isStrict ||
        (ast.body[0] && _isUseStrict(ast.body[0]));

    walk.recursive(ast, [, gVarBlock], _declaredVariableFinder);
    walk.recursive(ast, gVarBlock, _variableUsageCollector);
    return ast;
}

class Scope {
    /**
     * Construct Scope instance.
     * @param {Scope} paren
     * @param {Map.<string, AVal>} varMap
     * @param {VarBlock} vb
     */
    constructor(paren, varMap, vb) {
        this.paren = paren;
        this.varMap = varMap;
        this.vb = vb;
        if (vb.blockType === VarBlock.blockTypes.catchBlock) {
            // Collect thrown into .caughtAVal, and connect to parameter pattern
            this.caughtAVal = new types.AVal;
        }
    }

    /**
     * Find AVal of `varName` in the chain
     * @param {string} varName
     * @return {AVal}
     */
    getAValOf(varName) {
        let curr = this;
        while (curr != null) {
            if (curr.varMap.has(varName)) {
                return curr.varMap.get(varName);
            }
            curr = curr.paren;
        }
        // returns dummy AVal for not found variables
        return types.AValNull;
    }

    /**
     * Finds the first scope that is not for catch or normal block.
     * @return {Scope}
     */
    removeInitialCatchOrNormalBlocks() {
        let curr = this;
        while (curr.vb.isCatchBlock() || curr.vb.isNormalBlock()) {
            curr = curr.paren;
        }
        return curr;
    }
}
