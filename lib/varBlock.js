/*
 JavaScript는 global, function block, catch block에 변수가 달린다.
 ES6는 일반 block에도 달린다.

 VarBlock는 각 block에 달린 변수들을 나타낸다.
 - paren      : BlockVars, 바깥 block을 나타내는 객체
 - originLabel: number, 해당 BlockVars가 선언된 AST node의 @label
    origin이 될 수 있는 node는
    Function.body, CatchClause.block 두가지다.
    두가지 모두 BlockStatement이다.
 - isCatch    : boolean,
   * true  -> catch block
   * false -> function block, or global

 - paramVarNames : 매개변수 이름 목록, 매개 변수 순서대로
 - localVarNames : 지역 변수 이름 목록, 순서 무의미
    arguments를 사용하는 경우 localVarNames에 등장하고,
    arguments object를 사용하면 useArgumentsObject == true

 - (optional) useArgumentsObject: boolean
    함수 body block인 경우에만 사용 가능
    * true  : arguments object가 사용되었다.
      즉 함수 body에서 변수 arguments를 선언 없이 사용했다.
      이 경우, arguments는 함수의 지역 변수로 등록된다.
    * false 인 경우는 없다. 그럴거면 아예 변수 자체가 없다.

 - usedVariables : 각 block의 매개변수, 지역변수 중
   사용되는 위치가 있는 것들의 목록

 - instances : Delta -> VarBlock의 변수들 -> AVal
   getInstance(delta) 를 통해 같은 delta는 같은 mapping 주게 만듬

 - scopeInstances : [Scope]
   현재 VarBlock을 마지막으로 하는 Scope를 모두 모은다.
   getScopeInstance(delta, paren) 을 통해 같은 scope chain은
   같은 객체가 되도록 만든다.
*/
'use strict';

import * as types from './domains/types'
import * as myWalker from './util/myWalker'
const walk = require('acorn/dist/walk');
const aux = require('./aux');

export class VarBlock {
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

    isGlobal() {
        return this.blockType === VarBlock.blockTypes.globalBlock;
        // return this.paren == null;
    }

    isFunction() {
        return this.blockType === VarBlock.blockTypes.functionBlock;
        // return this.paren != null && this.localVarNames != null;
    }

    isCatchBlock() {
        return this.blockType === VarBlock.blockTypes.catchBlock;
        // return this.isCatch;
    }

    isNormalBlock() {
        return this.blockType === VarBlock.blockTypes.normalBlock;
        // return this.isCatch;
    }

    getLocalVarNames() {
        return this.localVarNames;
    }

    getParamVarNames() {
        return this.paramVarNames;
    }

    getVarNames() {
        return this.getLocalVarNames().concat(this.getParamVarNames());
    }

    hasLocalVar(varName) {
        return this.localVarNames && this.localVarNames.indexOf(varName) > -1;
    }

    hasParamVar(varName) {
        return this.paramVarNames.indexOf(varName) > -1;
    }

    hasVar(varName) {
        return this.hasParamVar(varName) || this.hasLocalVar(varName);
    }

    addDeclaredLocalVar(varName, dType) {
        let currBlock = this;
        switch(dType) {
            case VarBlock.declarationTypes.varDeclaration:
                // Go up until function or global
                while (!currBlock.isFunction() && !currBlock.isGlobal()) {
                    currBlock = currBlock.paren;
                }
                break;
            case VarBlock.declarationTypes.functionDeclaration:
                // Go up until function or global
                // or catch block having varName as its parameter
                // TODO: Be strict in strict mode
                // In strict mode, function declaration should in global or function block
                // However, it is not clear how to handle them. ignore?
                while (!currBlock.isFunction() && !currBlock.isGlobal() &&
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

    addParamVar(varName) {
        this.paramVarNames.push(varName);
    }

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

    addUsedVar(varName) {
        if (this.usedVariables.indexOf(varName) === -1) {
            this.usedVariables.push(varName);
        }
    }

    getUsedVarNames() {
        return this.usedVariables;
    }

    isUsedVar(varName) {
        return this.usedVariables.indexOf(varName) > -1;
    }

    // returns a mapping
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

    // returns an array
    getParamAVals(delta) {
        const instance = this.getInstance(delta);
        const params = [];
        this.getParamVarNames().forEach(name => {
            params.push(instance.get(name));
        });
        return params;
    }

    // returns an AVal
    getArgumentsAVal(delta) {
        if (!this.useArgumentsObject) {
            throw new Error('Not for this VarBlock');
        }
        return this.getInstance(delta).get('arguments');
    }

    // get a Scope instance
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

    // get function's scope instances
    getScopeWithParent(pScope) {
        const instances = new Set();
        this.scopeInstances.forEach(sc => {
            if (sc.paren === pScope) instances.add(sc);
        });
        return instances;
    }
}

VarBlock.blockTypes = {
    globalBlock: Symbol('global'),
    functionBlock: Symbol('function'),
    catchBlock: Symbol('catch'),
    normalBlock: Symbol('normal')
};

VarBlock.declarationTypes = {
    letDeclaration: Symbol('let'),
    constDeclaration: Symbol('const'),
    varDeclaration: Symbol('var'),
    functionDeclaration: Symbol('function'),
    implicitGlobalDeclaration: Symbol('implicit global')
};

/**
 * Check whether the stmt is the directive for strictness.
 * Taken from acorn
 * @param stmt - the first statement of a body
 * @returns {boolean}
 */
function isUseStrict(stmt) {
    return stmt.type === 'ExpressionStatement' &&
        stmt.expression.type === 'Literal' &&
        stmt.expression.raw.slice(1, -1) === 'use strict';
}


const declaredVariableFinder = walk.make({
    Function: (node, currBlock, c) => {
        let parenBlock = currBlock;
        if (node.id) {
            const funcName = node.id.name;
            parenBlock = currBlock.addDeclaredLocalVar(funcName,
                VarBlock.declarationTypes.functionDeclaration);
        }
        // compute strictness inside the function
        const strictIn = currBlock.isStrict ||
            (node.body.body[0] && isUseStrict(node.body.body[0]));
        // create a VarBlock for function
        const funcBlock = new VarBlock(
            parenBlock,
            node,
            VarBlock.blockTypes.functionBlock,
            strictIn
        );
        node.body['@block'] = funcBlock;
        // add function parameters to the scope
        for (let i = 0; i < node.params.length; i++) {
            const paramName = node.params[i].name;
            funcBlock.addParamVar(paramName);
        }
        walk.base.BlockStatement(node.body, funcBlock, c);
    },

    ForStatement: (node, currBlock, c) => {
        let forBlock;
        if (currBlock.isStrict) {
            forBlock = new VarBlock(
                currBlock,
                node,
                VarBlock.blockTypes.catchBlock,
                currBlock.isStrict
            );
            node['@block'] = forBlock;
        } else {
            forBlock = currBlock;
        }
        if (node.init) c(node.init, forBlock, 'ForInit');
        if (node.test) c(node.test, forBlock, 'Expression');
        if (node.update) c(node.update, forBlock, 'Expression');
        // its body can have a separate block.
        c(node.body, forBlock, undefined);
    },

    VariableDeclaration: (node, currBlock, c) => {
        let decl;
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
            decl = node.declarations[i];
            const name = decl.id.name;
            // TODO: Need to pass the decl type: const, let or var
            currBlock.addDeclaredLocalVar(name, dType);
        }
        if (decl.init) c(decl.init, currBlock, undefined);
    },

    TryStatement: (node, currScope, c) => {
        c(node.block, currScope, undefined);
        if (node.handler) {
            c(node.handler, currScope, undefined);
        }
        if (node.finalizer) {
            c(node.finalizer, currScope, undefined);
        }
    },

    CatchClause: (node, currBlock, c) => {
        const catchBlock = new VarBlock(
            currBlock,
            node,
            VarBlock.blockTypes.catchBlock,
            currBlock.isStrict
        );
        catchBlock.addParamVar(node.param.name);
        node.body['@block'] = catchBlock;
        walk.base.BlockStatement(node.body, catchBlock, c);
    },

    // Create VarBlock of type normalBlock
    BlockStatement: (node, currBlock, c) => {
        let inBlock;
        if (currBlock.isStrict) {
            inBlock = new VarBlock(
                currBlock,
                node,
                VarBlock.blockTypes.catchBlock,
                currBlock.isStrict
            );
            node['@block'] = inBlock;
        } else {
            inBlock = currBlock;
        }
        walk.base.BlockStatement(node, inBlock, c);
    }
});

// For variables in global and arguments in functions
const variableUsageCollector = walk.make({
    VariablePattern: (node, currBlock, c) => {
        c(node, currBlock, 'Identifier');
    },

    Identifier: (node, currBlock, c) => {
        if (myWalker.isDummyIdNode(node)) {
            // Skip dummy Id node
            return;
        }
        let containingBlock;
        const varName = node.name;
        if (varName !== 'arguments') {
            containingBlock = currBlock.findVarInChain(varName);
            if (containingBlock) {
                containingBlock.addUsedVar(varName);
                if (containingBlock.isGlobal()) {
                    containingBlock.addDeclaredLocalVar(varName,
                        VarBlock.declarationTypes.implicitGlobalDeclaration);
                }
            }
        } else {
            // varName == 'arguments'
            containingBlock = currBlock;
            // Note that
            // 1) normal block cannot have 'arguments' as its variable
            // 2) in strict mode catch parameter cannot be 'arguments'
            // In such cases, the containing block should be the nearest function block.
            while (containingBlock.isNormalBlock() ||
                   (containingBlock.isCatchBlock() &&
                    (containingBlock.isStrict || !containingBlock.hasParamVar(varName)))) {
                containingBlock = containingBlock.paren;
            }
            if (containingBlock.hasVar(varName)) {
                // arguments is explicitly declared
                containingBlock.addUsedVar(varName);
            } else {
                // arguments is not explicitly declared
                // add it as local variable considering it as a 'var' declaration
                containingBlock.addDeclaredLocalVar(varName,
                    VarBlock.declarationTypes.varDeclaration);
                // also it is used
                containingBlock.addUsedVar(varName);
                if (containingBlock.isFunction()) {
                    containingBlock.useArgumentsObject = true;
                }
            }
        }
    },

    ReturnStatement: (node, currBlock, c) => {
        let functionBlock = currBlock;
        while (functionBlock.isCatchBlock()) {
            functionBlock = functionBlock.paren;
        }
        if (!functionBlock.isGlobal() && node.argument !== null) {
            functionBlock.useReturnWithArgument = true;
        }
        if (node.argument) {
            c(node.argument, currBlock, undefined);
        }
    },

    ScopeBody: (node, currBlock, c) => {
        c(node, node['@block'] || currBlock);
    },

    BlockStatement: (node, currBlock, c) => {
        // Process BlockStatement with changed VarBlock
        walk.base.BlockStatement(node, node['@block'] || currBlock, c);
    }
});


export function annotateBlockInfo(ast, gVarBlock) {
    ast['@block'] = gVarBlock;

    gVarBlock.isStrict = gVarBlock.isStrict ||
        (ast.body[0] && isUseStrict(ast.body[0]));

    walk.recursive(ast, gVarBlock, declaredVariableFinder);
    walk.recursive(ast, gVarBlock, variableUsageCollector);
    return ast;
}

// define Scope class
class Scope {
    constructor(paren, varMap, vb) {
        this.paren = paren;
        this.varMap = varMap;
        this.vb = vb;
    }

    // find AVal of a variable in the chain
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

    // remove initial catch scopes from the chain
    removeInitialCatchOrNormalBlocks() {
        let curr = this;
        while (curr.vb.isCatchBlock() || curr.vb.isNormalBlock()) {
            curr = curr.paren;
        }
        return curr;
    }
}
