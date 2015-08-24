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
const walk = require('acorn/dist/walk');
const aux = require('./aux');

export class VarBlock {
    constructor(paren, originNode, isCatch) {
        this.paren = paren;
        this.originNode = originNode;
        this.originLabel = originNode['@label'];
        this.isCatch = isCatch;
        this.paramVarNames = [];
        this.localVarNames = [];

        this.usedVariables = [];
        // this.useArgumentsObject
        this.instances = new Map();
        this.scopeInstances = [];
    }

    isGlobal() {
        return this.paren == null;
    }

    isFunction() {
        return this.paren != null && this.localVarNames != null;
    }

    isCatchBlock() {
        return this.isCatch;
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

    addDeclaredLocalVar(varName, isFunDecl) {
        let currBlock = this;
        // peel off initial catch blocks
        // for function decl, skip any catch blocks,
        // for variable decl, skip catch block with different varName.
        while (currBlock.isCatchBlock() &&
        (isFunDecl || !currBlock.hasParamVar(varName))) {
            currBlock = currBlock.paren;
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
        while (currBlock && currBlock.paren && !currBlock.hasVar(varName)) {
            currBlock = currBlock.paren;
        }
        // if not found, it will return the global
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
            params.push(instance[aux.internalName(name)]);
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
}

const declaredVariableFinder = walk.make({
    Function: (node, currBlock, c) => {
        let parenBlock = currBlock;
        if (node.id) {
            const funcName = node.id.name;
            parenBlock = currBlock.addDeclaredLocalVar(funcName, true);
        }
        // create a VarBlock for function
        const funcBlock = new VarBlock(parenBlock, node);
        node.body['@block'] = funcBlock;
        // add function parameters to the scope
        for (let i = 0; i < node.params.length; i++) {
            const paramName = node.params[i].name;
            funcBlock.addParamVar(paramName);
        }
        c(node.body, funcBlock, undefined);
    },
    VariableDeclaration: (node, currBlock, c) => {
        let decl;
        for (let i = 0; i < node.declarations.length; i++) {
            decl = node.declarations[i];
            const name = decl.id.name;
            currBlock.addDeclaredLocalVar(name);
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
        const catchBlock = new VarBlock(currBlock, node, true);
        catchBlock.addParamVar(node.param.name);
        node.body['@block'] = catchBlock;
        c(node.body, catchBlock, undefined);
    }
});

// For variables in global and arguments in functions
const variableUsageCollector = walk.make({
    VariablePattern: (node, currBlock, c) => {
        c(node, currBlock, 'Identifier');
    },

    Identifier: (node, currBlock, c) => {
        let containingBlock;
        const varName = node.name;
        if (varName !== 'arguments') {
            containingBlock = currBlock.findVarInChain(varName);
            if (containingBlock.isGlobal()) {
                containingBlock.addDeclaredLocalVar(varName);
            }
            containingBlock.addUsedVar(varName);
        } else {
            // varName == 'arguments'
            containingBlock = currBlock;
            while (containingBlock.isCatchBlock() &&
                    !containingBlock.hasParamVar(varName)) {
                containingBlock = containingBlock.paren;
            }
            if (containingBlock.hasVar(varName)) {
                // arguments is explicitly declared
                containingBlock.addUsedVar(varName);
            } else {
                // arguments is not explicitly declared
                // add it as local variable
                containingBlock.addDeclaredLocalVar(varName);
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
    }
});


export function annotateBlockInfo(ast, gBlock) {
    if (!gBlock) {
        // when global block is not given, create
        gBlock = new VarBlock(null, ast);
    }
    ast['@block'] = gBlock;
    walk.recursive(ast, gBlock, null, declaredVariableFinder);
    walk.recursive(ast, gBlock, null, variableUsageCollector);
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
        throw new Error('Should have found the variable');
    }

    // remove initial catch scopes from the chain
    removeInitialCatchBlocks() {
        let curr = this;
        while (curr.vb.isCatchBlock()) {
            curr = curr.paren;
        }
        return curr;
    }
}
