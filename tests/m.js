function FnType(name, argNames, argAbsVals) {
    // its __proto__ should be Function.prototype
    // for now it is AbsVal representing null - TODO use the correct proto
    ObjType.call(this, new AbsVal(PrimNumber), name);
    //ObjType.call(this, new AbsVal, name);
    this.thisAbsVal = new AbsVal;
    this.paramNames = argNames;
    this.paramAbsVals = argAbsVals;
    this.retAbsVal = new AbsVal;
}