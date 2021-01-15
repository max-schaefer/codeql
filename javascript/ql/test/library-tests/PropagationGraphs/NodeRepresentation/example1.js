db.collection('Employee').updateOne({
    "EmployeeName": "NewEmployee" // candidateRep: rhs (member * (parameter 0 (member updateOne *)))
}, {
    $set: { // candidateRep: rhs (member * (parameter 1 (member updateOne *)))
        "EmployeeName": "Mohan"
    }
});

global.variable = 0; // candidateRep: rhs (member variable (global))

module.exports.f = function () { // candidateRep: rhs (member f (member exports *))
    return 0; // candidateRep: rhs (return (member f (member exports *)))
};

module.exports = 0; // candidateRep: rhs (member exports *)
