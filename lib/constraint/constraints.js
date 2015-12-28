/**
 * @file Defines CSTR and its subclasses.
 * @author sewon326.kim@samsung.com
 */

'use strict';
import * as types from '../domains/types'
import * as status from '../domains/status'
import * as csc from '../domains/context'
import * as cGen from './cGen'

class CSTR {
    /**
     * Checks the equality between CSTRs.
     * @param {CSTR} other
     * @return {boolean}
     */
    equals(other) {
        return this === other;
    }

    /**
     * Adds type using the information of CSTR.
     * @abstract
     * @param {Type} type
     */
    addType(type) {
        throw new Error("calling abstract method");
    }
}

export class ReadProp extends CSTR {
    /**
     * Constructs ReadProp.
     * @param {string|null} prop
     * @param {AVal} to
     */
    constructor(prop, to) {
        super();
        this.prop = prop;
        this.to = to;
    }

    /**
     * @override
     */
    addType(obj) {
        if (!(obj instanceof (types.ObjType))) return;
        // when obj is ObjType,
        const ownProp = obj.getProp(this.prop, true);
        if (ownProp) {
            // when the object has the prop,
            ownProp.propagate(this.to);
        } else if (obj.getProp('__proto__', true)) {
            // Propagate from unknown prop if obj has it.
            if (obj.hasProp(null)) {
                obj.getProp(null, true).propagate(this.to);
            }
            // use prototype chain
            obj.getProp('__proto__').propagate(this);
        }
    }

    /**
     * @override
     */
    equals(other) {
        if (!(other instanceof ReadProp)) return false;
        return this.prop === other.prop
            && this.to.equals(other.to);
    }
}

export class WriteProp extends CSTR {
    /**
     * Constructs WriteProp.
     * @param {string|null} prop
     * @param {AVal} from
     */
    constructor(prop, from) {
        super();
        this.prop = prop;
        this.from = from;
    }

    /**
     * @override
     */
    addType(obj) {
        if (!(obj instanceof (types.ObjType))) return;
        const ownProp = obj.getProp(this.prop);
        this.from.propagate(ownProp);
        // Handle 'prototypeOf' when writing to 'prototype'
        if (this.prop === 'prototype') {
            this.from.getTypes().forEach((tp) => {
                tp.prototypeOf.addType(obj);
            });
        }
        // When assigning FnType to a prop,
        this.from.getTypes().forEach((fn) => {
            if (!(fn instanceof (types.FnType))) return;
            // obj's prototypeOf => selfAVal of null context
            const [selfAVal,,] = fn.getFunEnv(csc.CallSiteContext.nullContext);
            obj.prototypeOf.getTypes().forEach((ctor) => {
                if (ctor instanceof (types.FnType))
                    selfAVal.addType(ctor.getInstance());
            });
        });
    }
}

export class IsAdded extends CSTR {
    /**
     * Constructs IsAdded.
     * @param {AVal} other
     * @param {AVal} target
     */
    constructor(other, target) {
        super();
        this.other = other;
        this.target = target;
    }

    /**
     * @override
     */
    addType(type) {
        if ((type === types.PrimNumber
            || type === types.PrimBoolean)
            && (this.other.hasType(types.PrimNumber)
            || this.other.hasType(types.PrimBoolean))) {
            this.target.addType(types.PrimNumber);
        }
        if (type === types.PrimString
            && !this.other.isEmpty()) {
            this.target.addType(types.PrimString);
        }
    }
}

function _prepareRestAValFromArgs(node, curStatus, args, startIndex) {
    const restAVal = cGen.getRestAVal(node, curStatus);
    for (let i = startIndex; i < args.length; i++) {
        restAVal.propagate(new WriteProp(String(i - startIndex), args[i]));
        restAVal.propagate(new WriteProp(null, args[i]));
    }
    return restAVal;
}

function _connectToParameter(params, funStatus, args) {
    for (let i = 0; i < args.length && i < params.length; i++) {
        if (params[i].type === 'RestElement') {
            let restAVal = _prepareRestAValFromArgs(params[i], funStatus, args, i);
            cGen.connectPattern(params[i], funStatus, restAVal);
            break;
        }
        // Using funStatus for analyzing defaults is safe
        cGen.connectPattern(params[i], funStatus, args[i]);
    }
}

export class IsCallee extends CSTR {
    /**
     * Constructs IsCallee.
     * @param {AVal} self
     * @param {Array.<AVal>} args
     * @param {AVal} ret
     * @param {AVal} exc
     * @param {CallSiteContext} delta
     */
    constructor(self, args, ret, exc, delta) {
        super();
        this.self = self;
        this.args = args;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
    }

    /**
     * @override
     */
    addType(f) {
        if (!(f instanceof (types.FnType))) return;
        const fBlock = f.originNode.body['@block'];
        const cBlock = fBlock.hasParamScope ? fBlock.paren : fBlock;
        const deltaFn = this.delta.truncateFor(f);
        const [selfAVal, retAVal, excAVal] = f.getFunEnv(deltaFn);
        const newSC = cBlock.getScopeInstance(f.sc, deltaFn);
        const funStatus
            = new status.Status(selfAVal, retAVal, excAVal,
            deltaFn, newSC);

        // arrow function should use boundThis and ignore the receiver AVal
        const effectiveSelf = f.boundThis ? f.boundThis : this.self;
        effectiveSelf.propagate(selfAVal);

        _connectToParameter(f.originNode.params, funStatus, this.args);

        // for arguments object
        if (f.originNode.body['@block'].useArgumentsObject) {
            const argObj = f.getArgumentsObject(deltaFn);
            newSC.getAValOf('arguments').addType(argObj);
            for (let i = 0; i < this.args.length; i++) {
                this.args[i].propagate(argObj.getProp(i + ''));
                this.args[i].propagate(argObj.getProp(null));
            }
            argObj.getProp('callee').addType(f);
            argObj.getProp('length').addType(types.PrimNumber);
        }

        // constraint generation for the function body
        cGen.addConstraints(f.originNode.body, funStatus);

        // get return
        retAVal.propagate(this.ret);
        // get exception
        excAVal.propagate(this.exc);
    }
}

export class IsCtor extends CSTR {
    /**
     * Constructs IsCtor.
     * @param {Array.<AVal>}args
     * @param {AVal} ret
     * @param {AVal} exc
     * @param {AVal} delta
     */
    constructor(args, ret, exc, delta) {
        super();
        this.args = args;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
    }

    /**
     * @override
     */
    addType(f) {
        // Only non-arrow functions can create instances.
        if (!(f instanceof (types.FnType)) || f.boundThis) {
            return;
        }
        const deltaFn = this.delta.truncateFor(f);
        const [selfAVal, retAVal, excAVal] = f.getFunEnv(deltaFn);
        const newSC = f.originNode.body['@block'].getScopeInstance(f.sc, deltaFn);
        const funStatus
            = new status.Status(
            selfAVal,
            // In constructor, we can explicitly return only ObjType.
            new IfObjType(retAVal),
            excAVal,
            deltaFn,
            newSC);
        // f's instance is bound to 'this.'
        const newObj = f.getInstance();
        selfAVal.addType(newObj);

        _connectToParameter(f.originNode.params, funStatus, this.args);

        // for arguments object
        if (f.originNode.body['@block'].useArgumentsObject) {
            const argObj = f.getArgumentsObject(deltaFn);
            newSC.getAValOf('arguments').addType(argObj);
            for (let i = 0; i < this.args.length; i++) {
                this.args[i].propagate(argObj.getProp(i + ''));
                this.args[i].propagate(argObj.getProp(null));
            }
            argObj.getProp('callee').addType(f);
            argObj.getProp('length').addType(types.PrimNumber);
        }

        // constraint generation for the function body
        cGen.addConstraints(f.originNode.body, funStatus);

        // provide two kinds of result of 'new'
        this.ret.addType(newObj);
        retAVal.propagate(this.ret);
        // get exception
        excAVal.propagate(this.exc);
    }
}

// ignore non object types
class IfObjType extends CSTR {
    /**
     * Constructs IfObjType.
     * @param {AVal} aval
     */
    constructor(aval) {
        super();
        this.aval = aval;
    }

    /**
     * @override
     */
    addType(type) {
        if (!(type instanceof types.ObjType)) return;
        this.aval.addType(type);
    }
}
