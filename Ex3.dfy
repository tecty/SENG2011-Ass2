class {:autocontracts} Dishwasher
{
    var detergented:bool;
    var loaded:bool;
    var washed:bool;
    predicate Valid()
    {
        // this state is not existed 
        !loaded && washed ==> false
    }

    constructor ()
        // all set to false 
        ensures this.detergented == false
        ensures this.loaded      == false
        ensures this.washed      == false
    {
        this.loaded       := false;
        this.detergented  := false;
        this.washed       := false;
    }

    method Load()
        ensures this.loaded == true
        ensures this.washed == false
    {
        this.loaded := true;
        this.washed := false;
    }

    method Unload()
        requires this.loaded
        requires this.washed
        ensures this.loaded == false;
        ensures this.washed == false;
    {
        this.loaded := false;
        this.washed := false;
    }

    method AddDtgt()
        ensures this.detergented == true
    {
        this.detergented := true;
    }

    method Wash()
        requires this.detergented == true;
        requires this.loaded      == true;
        ensures  this.detergented == false
        ensures  this.washed      == true;
    {
        this.detergented := false;
        this.washed      := true;
    }
}