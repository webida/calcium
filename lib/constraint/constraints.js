'use strict';

import * as types from '../domains/types'
import * as status from '../domains/status'
import * as csc from '../domains/context'
const cGen = require('./cGen');

function CSTR() {}
CSTR.prototype = Object.create(null);
CSTR.prototype.equals = function (other) {
    return this === other;
};

function ReadProp(prop, to) {
    this.prop = prop;
    this.to = to;
}
ReadProp.prototype = Object.create(CSTR.prototype);
ReadProp.prototype.addType = function (obj) {
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
        obj.getProp('__proto__')
          .propagate(new ReadProp(this.prop, this.to));
    }
};
ReadProp.prototype.equals = function (other) {
    if (!(other instanceof ReadProp)) return false;
    return this.prop === other.prop
        && this.to.equals(other.to);
};

function WriteProp(prop, from) {
    this.prop = prop;
    this.from = from;
}
WriteProp.prototype = Object.create(CSTR.prototype);
WriteProp.prototype.addType = function (obj) {
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
};

function IsAdded(other, target) {
    this.other = other;
    this.target = target;
}
IsAdded.prototype = Object.create(CSTR.prototype);
IsAdded.prototype.addType = function (type) {
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
};

function IsCallee(self, args, ret, exc, delta) {
    this.self = self;
    this.args = args;
    this.ret = ret;
    this.exc = exc;
    this.delta = delta;
}
IsCallee.prototype = Object.create(CSTR.prototype);
IsCallee.prototype.addType = function (f) {
    if (!(f instanceof (types.FnType))) return;
    const deltaFn = this.delta.truncateFor(f);
    const [selfAVal, retAVal, excAVal] = f.getFunEnv(deltaFn);
    const newSC = f.originNode.body['@block'].getScopeInstance(f.sc, deltaFn);
    const funStatus
        = new status.Status(selfAVal, retAVal, excAVal,
                            deltaFn, newSC);
    // pass this object
    this.self.propagate(selfAVal);

    const minLen = Math.min(this.args.length, f.paramNames.length);
    for (let i = 0; i < minLen; i++) {
        this.args[i].propagate(newSC.getAValOf(f.paramNames[i]));
    }

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
};

function IsCtor(args, ret, exc, delta) {
    this.args = args;
    this.ret = ret;
    this.exc = exc;
    this.delta = delta;
}
IsCtor.prototype = Object.create(CSTR.prototype);
IsCtor.prototype.addType = function (f) {
    if (!(f instanceof (types.FnType))) return;
    const deltaFn = this.delta.truncateFor(f);
    const [selfAVal, retAVal, excAVal] = f.getFunEnv(deltaFn);
    const newSC = f.originNode.body['@block'].getScopeInstance(f.sc, deltaFn);
    const funStatus
        = new status.Status(selfAVal, new IfObjType(retAVal), excAVal,
                            deltaFn, newSC);
    // pass this object
    const newObj = f.getInstance();
    selfAVal.addType(newObj);

    const minLen = Math.min(this.args.length, f.paramNames.length);
    for (let i = 0; i < minLen; i++) {
        this.args[i].propagate(newSC.getAValOf(f.paramNames[i]));
    }

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

    // by explicit return, only ObjType are propagated
    retAVal.propagate(this.ret);
    // return new object
    this.ret.addType(newObj);
    // get exception
    excAVal.propagate(this.exc);
};

// ignore non object types
function IfObjType(aval) {
    this.aval = aval;
}
IfObjType.prototype = Object.create(CSTR.prototype);
IfObjType.prototype.addType = function (type) {
    if (!(type instanceof types.ObjType)) return;
    this.aval.addType(type);
};

exports.ReadProp = ReadProp;
exports.WriteProp = WriteProp;
exports.IsAdded = IsAdded;
exports.IsCallee = IsCallee;
exports.IsCtor = IsCtor;
