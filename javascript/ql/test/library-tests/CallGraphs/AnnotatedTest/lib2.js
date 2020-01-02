/** name:lib2.factory */
module.exports = function factory() {
    /** name:lib2.factory.fn */
    function fn(x) {
        console.log(x);
    }
    return fn;
};
