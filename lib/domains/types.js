// for DEBUG
var count = 0;
/**
 * the abstract value for a concrete value
 * which is a set of types.
 */
export class AVal {
    /**
     * @param {Type} type - give a type to make AVal with a single type
     */
    constructor(type) {
        // type: contained types
        // We assume types are distinguishable by '==='
        if (type) this.types = new Set([type]);
        else this.types = new Set();
        // forwards: propagation targets
        // We assume targets are distinguishable by 'equals' method
        this.forwards = new Set();
        // for DEBUG
        this._id = count++;
    }

    /** Check whether it has any type
     * @returns {boolean}
     */
    isEmpty() {
        return this.types.size === 0;
    }

    /**
     * @returns {[Type]}
     */
    getTypes() {
        return this.types;
    }

    /**
     * @param {Type} type
     * @returns {boolean}
     */
    hasType(type) {
        return this.types.has(type);
    }

    /**
     * Add a type.
     * @param {Type} type
     */
    addType(type) {
        if (this.types.has(type)) return;
        // given type is new
        this.types.add(type);
        // send to propagation targats
        this.forwards.forEach(function (fwd) {
            fwd.addType(type);
        });
    }

    /**
     * @param {AVal} target
     */
    propagate(target) {
        if (!this.addForward(target)) return;
        // target is newly added
        // send types to the new target
        this.types.forEach(function (type) {
            target.addType(type);
        });
    }

    /**
     * Add a propagation target
     * @param {AVal} fwd
     * @returns {boolean} - returns false if it already has the target
     */
    addForward(fwd) {
        for (let oldFwd of this.forwards) {
            if (fwd.equals(oldFwd)) return false;
        }
        this.forwards.add(fwd);
        return true;
    }

    /**
     * Check if they are the same
     * @param {AVal} other
     * @returns {boolean}
     */
    equals(other) {
        // simple reference comparison
        return this === other;
    }

    /**
     * TODO: check whether we really need this method.
     * @param {string} prop
     * @returns {AVal}
     */
    getProp(prop) {
        if (prop === '✖') {
            // ✖ is the bogus property name added for error recovery.
            return AValNull;
        }
        if (this.props.has(prop)) {
            return this.props.get(prop);
        } else {
            return AValNull;
        }
    }
}

/**
 * the super class of all types
 * each type should be distinguishable by '===' operation.
 */
class Type {
    /**
     * Create a new type
     * @param {string} name
     */
    constructor(name) {
        this.name = name;
    }

    /**
     * Returns the name of type
     * @returns {string}
     */
    getName() {
        return this.name;
    }

    /**
     * Default implementation for toString
     * This should be overridden for sophisticated types
     * @returns {string}
     */
    toString() {
        return getName();
    }
}


/**
 * 1. object types
 */
export class ObjType extends Type {
    /**
     * @param {AVal} proto - AVal of constructor's prototype
     * @param {string} name - guessed name
     */
    constructor(proto, name) {
        super(name);
        this.props = new Map();
        // share proto with __proto__
        this.setProp('__proto__', proto);
    }

    /**
     * @param {string|null} prop - null for computed props
     * @param {boolean} readOnly - if false, create AVal for prop if necessary
     * @returns {AVal} AVal of the property
     */
    getProp(prop, readOnly) {
        if (prop === '✖') {
            // ✖ is the bogus property name added during parsing error recovery.
            return AValNull;
        }
        if (this.props.has(prop)) {
            return this.props.get(prop);
        } else if (readOnly) {
            return null;
        } else {
            var newPropAVal = new AVal;
            this.props.set(prop, newPropAVal);
            return newPropAVal;
        }
    }

    /**
     * We use this function to share .prototype with instances __proto__
     * It is possible to use this function to merge AVals to optimize the analyzer.
     * @param {string|null} prop - null for computed props
     * @param {AVal} aval
     */
    setProp(prop, aval) {
        if (prop === '✖') {
            // ✖ is the bogus property name added during parsing error recovery.
            return;
        }
        this.props.set(prop, aval);
    }

    /**
     * TODO: Check this function's necessity
     * @param {string} prop
     * @returns {boolean}
     */
    hasProp(prop) {
        if (prop === '✖') return false;
        return this.props.has(prop);
    }

    /**
     * TODO: Check this function's necessity
     * @param {Type} type
     * @param {string} prop
     */
    addTypeToProp(type, prop) {
        if (prop === '✖') return;
        if (!this.props.has(prop)) {
            this.props.set(prop, new AVal);
        }
        if (this.props.get(prop).hasType(type)) return;
        this.props.get(prop).addType(type);
    }

    /**
     * TODO: Check this function's necessity
     * @param {AVal} aval
     * @param {string} prop
     */
    joinAValToProp(aval, prop) {
        var self = this;
        aval.getTypes().forEach(function (type) {
            self.addTypeToProp(type, prop);
        });
    }
}

// make an Obj from the global scope
export function mkObjFromGlobalScope(gScope) {
    var gObj = new ObjType(AValNull, '*global scope*');
    gObj.props = gScope.varMap;
    // Override getProp method for global object
    // We ignore 'readOnly' parameter to always return its own prop AVal 
    gObj.getProp = function (prop) {
        return ObjType.prototype.getProp.call(this, prop);
    };
    return gObj;
}

/**
 * 2. primitive types
 */
export class PrimType extends Type {
    /**
     * @param {string} name
     */
    constructor(name) {
        super(name);
    }
}

/**
 * 3. function types
 * the name is used for the type of the instances from the function
 */
export class FnType extends ObjType {
    /**
     * @param {AVal} fn_proto - AVal for constructor's .prototype
     * @param {string} name - guessed name
     * @param {[string]} argNames - list of parameter names
     * @param {Scope} sc - functions scope chain, or closure
     * @param {node} originNode - AST node for the function
     * @param {Type} argProto - prototype for arguments object
     */
    constructor(fn_proto, name, argNames, sc, originNode, argProto) {
        super(fn_proto, name);
        this.paramNames = argNames;
        this.sc = sc;
        this.originNode = originNode;
        this.argProto = argProto;
        // funEnv : CallContext -> [self, ret, exc]
        this.funEnv = new Map;
    }

    /**
     * construct Status for function
     * @param {CallContext} delta - call context
     * @returns {[AVal, AVal, AVal]} - for self, return and exception AVals
     */
    getFunEnv(delta) {
        if (this.funEnv.has(delta)) {
            return this.funEnv.get(delta);
        } else {
            var triple = [new AVal, new AVal, new AVal];
            this.funEnv.set(delta, triple);
            return triple;
        }
    }

    getArgumentsObject(delta) {
        this.argObjMap = this.argObjMap || new Map;
        if (this.argObjMap.has(delta)) {
            return this.argObjMap.get(delta);
        } else {
            var argObj = new ObjType(new AVal(this.argProto), '*arguments object*');
            this.argObjMap.set(delta, argObj);
            return argObj;
        }
    }

    /**
     * get Object made by the function
     * TODO: use additional information to create multiple instances
     * @returns {ObjType}
     */
    getInstance() {
        // objInstance is the object made by the functioann
        if (this.objInstance) return this.objInstance;
        // we unify constructor's .prototype and instance's __proto__
        this.objInstance = new ObjType(this.getProp('prototype'));
        return this.objInstance;
    }
}

/** 
 * 4. array types
 * @constructor
 */
export class ArrType extends ObjType {
    constructor(arr_proto) {
        super(arr_proto, 'Array');
    }
}

// Make primitive types
export const PrimNumber = new PrimType('number');
export const PrimString = new PrimType('string');
export const PrimBoolean = new PrimType('boolean');

// AbsNull represents all empty abstract values.
export const AValNull = new AVal();
// You should not add any properties to it.
AValNull.props = null;
// Adding types are ignored.
AValNull.addType = function () {};

export class AbsCache {
    constructor() {
        this.map = new Map();
    }

    /**
     * Get if one exists, if not create one
     * @param loc
     * @param ctx
     * @returns {*}
     */
    get(loc, ctx) {
        if (!this.map.has(loc)) {
            // create inner map
            this.map.set(loc, new Map());
        }
        const mapLoc = this.map.get(loc);
        if (!mapLoc.has(ctx)) {
            const av = new AVal();
            mapLoc.set(ctx, av);
            return av;
        } else {
            return mapLoc.get(ctx);
        }
    }

    /**
     * To use av made by others (e.g. scope)
     * @param loc
     * @param ctx
     * @param av
     */
    set(loc, ctx, av) {
        if (!this.map.has(loc)) {
            // create inner map
            this.map.set(loc, new Map());
        }
        this.map.get(loc).set(ctx, av);
    }

    /**
     * Check whether it has one for loc and ctx
     * @param loc
     * @param ctx
     * @returns {boolean}
     */
    has(loc, ctx) {
        return this.map.has(loc) && this.map.get(loc).has(ctx);
    }

    /**
     * Get all the types of the loc
     * @param loc
     * @returns [Type]
     */
    getTypeOfLoc(loc) {
        if (!this.map.has(loc)) {
            // no type is available
            return null;
        }
        const tps = [];
        for (var av of this.map.get(loc).values()) {
            for (var tp of av.getTypes()) {
                if (tps.indexOf(tp) === -1) {
                    tps.push(tp);
                }
            }
        }
        return tps;
    }
}
