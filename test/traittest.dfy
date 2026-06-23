
module ttest {
    trait Valid extends object {
        predicate Valid()
    }

    trait System<Model> {
        ghost var repr: set<object>
        var sys: object

        method foo(v: Valid) 
            modifies this`sys
        {
            this.sys := v;

        }
    }
}