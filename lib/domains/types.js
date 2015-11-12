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

    getSize() {
        return this.types.size;
    }

    /**
     * @returns {Set.<Type>}
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
     * @returns {boolean}
     */
    addType(type) {
        if (this.types.has(type)) {
            return false;
        }
        // given type is new
        this.types.add(type);
        // send to propagation targets
        this.forwards.forEach(fwd => {
            fwd.addType(type);
        });
        return true;
    }

    /**
     * @param {AVal} target
     */
    propagate(target) {
        if (!this.addForward(target)) return;
        // target is newly added
        // send types to the new target
        this.types.forEach(type => {
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
            if (fwd.equals(oldFwd)) {
                return false;
            }
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
     * @param {string|null} prop
     * @returns {AVal}
     */
    getProp(prop) {
        if (this.props.has(prop)) {
            return this.props.get(prop);
        } else {
            return AValNull;
        }
    }

    toString() {
        const visitedTypes = new Set();
        return this._toString(visitedTypes);
    }

    _toString(visitedTypes) {
        const typeStrings = [];
        for (let tp of this.types) {
            if (visitedTypes.has(tp)) {
                typeStrings.push('?');
            } else {
                typeStrings.push(tp._toString(visitedTypes));
            }
        }
        return typeStrings.join('|');
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
    _toString() {
        return this.getName();
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
        // remember whose prototype I am
        this.prototypeOf = new AVal();
    }

    /**
     * @param {string|null} prop - null for computed props
     * @param {boolean} readOnly - if false, create AVal for prop if necessary
     * @returns {AVal} AVal of the property
     */
    getProp(prop, readOnly) {
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
        this.props.set(prop, aval);
    }

    /**
     * Returns iterator of its own property names
     * @returns {Iterator.<string>}
     */
    getOwnPropNames() {
        return this.props.keys();
    }

    /**
     * TODO: Check this function's necessity
     * @param {string|null} prop
     * @returns {boolean}
     */
    hasProp(prop) {
        return this.props.has(prop);
    }

    /**
     * TODO: Check this function's necessity
     * @param {Type} type
     * @param {string|null} prop
     */
    addTypeToProp(type, prop) {
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

    /**
     * Show object's own property names
     * @param {Set.<Type>} visitedTypes
     * @returns {string}
     */
    _toString(visitedTypes) {
        if (this.name === undefined) {
            const props = [];
            for (let p of this.props.keys()) {
                // skipping __proto__
                if (p === '__proto__') continue;
                props.push(p);
            }
            return '{' + props.join() + '}';
        } else {
            return this.name;
        }
    }
}

// make an Obj from the global scope
export function mkObjFromGlobalScope(gScope) {
    var gObj = new ObjType(AValNull, '*global scope*');
    gObj.props = gScope.varMap;
    // Override getProp method for global object
    // We ignore 'readOnly' parameter to always return its own prop AVal 
    gObj.getProp = function (prop) {
        if (!gScope.vb.hasLocalVar(prop)) {
            // when we refer prop of the global object
            gScope.vb.addDeclaredLocalVar(prop);
        }
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
     * @param {AVal} boundThis - remember thisAVal for arrow function
     */
    constructor(fn_proto, name, argNames, sc, originNode, argProto, boundThis) {
        super(fn_proto, name);
        this.paramNames = argNames;
        this.sc = sc;
        this.originNode = originNode;
        if (argProto) {
            this.argProto = argProto;
        }
        if (boundThis) {
            this.boundThis = boundThis;
        }
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
        // objInstance is the object made by the function
        if (this.objInstance) return this.objInstance;
        // we unify constructor's .prototype and instance's __proto__
        this.objInstance = new ObjType(this.getProp('prototype'));
        return this.objInstance;
    }

    _stringifyOneLevelStructure(structure) {

        const params = structure.params.map(function (param) {
            if (param.type !== undefined)
                return param.name + ':' + param.type;
            else return param.name;
        });

        let resStr = 'fn(' + params.join(', ') + ')';
        if (structure.ret !== undefined) {
            resStr += ' -> ' + structure.ret;
        }
        return resStr;
    }

    _toString(visitedTypes) {
        if (visitedTypes.has(this)) {
            return '?';
        }
        const structure = this._getOneLevelStructure(visitedTypes);
        return this._stringifyOneLevelStructure(structure);
    }

    _getOneLevelStructure(visitedTypes) {
        visitedTypes.add(this);
        const fBlock = this.originNode.body['@block'];
        const pBlock = fBlock.hasParamScope ? fBlock.paren : fBlock;
        const paramScopes = pBlock.getScopeWithParent(this.sc);
        const params = this.originNode.params;


        function _concatNameAndType(name, typeString) {
            return name + (typeString ? ':' + typeString : '');
        }

        function _patternName(pattern) {
            switch (pattern.type) {
                case 'Identifier' :
                    return pattern.name;
                case 'AssignmentPattern' :
                    return pattern.left.name;
                case 'ObjectPattern' :
                    return '{' + pattern.properties.map((e) => _patternName(e.value)) + '}';
                case 'ArrayPattern' :
                    return '[' + pattern.elements.map(_patternName) + ']';
                case 'RestElement' :
                    return '...' + _patternName(pattern.argument);
            }
        }

        function _patternWithType(pattern, removeId) {
            switch (pattern.type) {
                case 'Identifier' :
                    if (removeId) return _getTypeStringForVar(pattern.name);
                    else return _concatNameAndType(pattern.name, _getTypeStringForVar(pattern.name));
                case 'AssignmentPattern' :
                    return _patternWithType(pattern.left);
                case 'ObjectPattern' :
                    return '{' + pattern.properties.map((e) => _patternWithType(e.value)) + '}';
                case 'ArrayPattern' :
                    return '[' + pattern.elements.map((e) => _patternWithType(e)) + ']';
                case 'RestElement' :
                    if (removeId) {
                        return _patternWithType(pattern.argument, removeId);
                    } else {
                        return '...' + _patternWithType(pattern.argument);
                    }

            }
        }

        function _getTypeStringForVar(varName) {
            const strings = [];
            let hasType = false;
            for (let sc of paramScopes) {
                const aval = sc.getAValOf(varName);
                if (!aval.isEmpty()) {
                    strings.push(aval._toString(visitedTypes));
                    hasType = true;
                }
            }
            return hasType ? strings.join('|') : undefined;
        }

        const paramInfo = params.map((p) => ({
            name: _patternName(p),
            type: _patternWithType(p, true)}));

        // computing joined retAVal
        const retTypeStrings = [];
        let noRetTypes = true;
        for (let [, retAVal, ] of this.funEnv.values()) {
            if (!retAVal.isEmpty()) {
                noRetTypes = false;
                retTypeStrings.push(retAVal._toString(visitedTypes));
            }
        }
        visitedTypes.delete(this);
        return {params: paramInfo, ret: (noRetTypes ? undefined : retTypeStrings.join('|'))};

    }

    getOneLevelStructure() {
        const visitedTypes = new Set();
        return this._getOneLevelStructure(visitedTypes);
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

    _toString(visitedTypes) {
        if (visitedTypes.has(this)) {
            return '?';
        }
        visitedTypes.add(this);
        // prop null is used for array elements
        const eltTypes = this.getProp(null, true);
        const tpStr = '[' + eltTypes._toString(visitedTypes) + ']';
        visitedTypes.delete(this);
        return tpStr;
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
     * Merge all AVal of the loc
     * @param loc
     * @returns {AVal}
     */
    getMergedAValOfLoc(loc) {
        if (!this.map.has(loc)) {
            // no type is available
            return null;
        }
        const mergedAVal = new AVal();
        if (this.map.has(loc)) {
            for (let av of this.map.get(loc).values()) {
                for (let tp of av.getTypes()) {
                    mergedAVal.addType(tp);
                }
            }
        }        return mergedAVal;
    }
}
