db.collection('Employee').updateOne({
    "EmployeeName": "NewEmployee" // candidateRep: rhs (member * (parameter 0 (member updateOne *)))
}, {
    $set: { // candidateRep: rhs (member * (parameter 1 (member updateOne *)))
        "EmployeeName": "Mohan"
    }
});