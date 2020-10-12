class C {
    foo() { } /* def (member foo (member exports (module export-instance))) */
}

module.exports = new C();
