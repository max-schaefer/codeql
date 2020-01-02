/** name:factory */
function factory() {
    /** name:factory.fn */
    function fn(x) {
        console.log(x);
    }
    return fn;
}
/** calls:factory */
const fn = factory();
/** calls:factory.fn */
fn();

const factory2 = require('./lib2.js');
/** calls:lib2.factory */
const fn2 = factory2();
/** calls:lib2.factory.fn */
fn2();
