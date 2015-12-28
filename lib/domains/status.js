/**
 * @file Defines Status.
 * @author sewon326.kim@samsung.com
 */
export class Status {
    /**
     * Constructs Status.
     * @param {AVal} self
     * @param {AVal} ret
     * @param {AVal} exc
     * @param {CallSiteContext} delta
     * @param {Scope} sc
     */
    constructor(self, ret, exc, delta, sc) {
        this.self = self;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
        this.sc = sc;
    }

    /**
     * Checks equality with other Status
     * @param {Status} other
     * @return {boolean}
     */
    equals(other) {
        return this.self === other.self &&
            this.ret === other.ret &&
            this.exc === other.exc &&
            this.delta === other.delta &&
            this.sc === other.sc;
    }

    /**
     * Returns a new Status,
     * whose instance fields are changed from `this` using `changedStatus`.
     * @param changeStatus
     * @return {Status}
     */
    getNewStatus(changeStatus) {
        const newStatus = new Status;
        for (let p in this) {
            if (this.hasOwnProperty(p)) {
                if (changeStatus.hasOwnProperty(p)) {
                    newStatus[p] = changeStatus[p];
                } else {
                    newStatus[p] = this[p];
                }
            }
        }
        return newStatus;
    }
}
