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

    constructor ()// all set to false 
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
        // things I woun't touch 
        ensures this.detergented == old(this.detergented)
    {
        this.loaded := true;
        this.washed := false;
    }

    method Unload()
        requires this.loaded
        requires this.washed
        ensures this.loaded == false;
        ensures this.washed == false;
        ensures this.detergented == old(this.detergented)
    {
        this.loaded := false;
        this.washed := false;
    }

    method AddDtgt()
        ensures this.detergented == true
        // things I won't changed 
        ensures this.loaded == old(this.loaded)
        ensures this.washed == old(this.washed)
    {
        this.detergented := true;
    }

    method Wash()
        requires this.detergented == true;
        requires this.loaded      == true;
        ensures  this.detergented == false
        ensures  this.washed      == true;
        ensures  this.loaded      == old(this.loaded);
    {
        this.detergented := false;
        this.washed      := true;
    }
}

method Test1()
{
    var w := new Dishwasher();
    w.Load();
    w.AddDtgt();
    w.Wash();
    w.Unload();
}

method Test2()
{
    var w := new Dishwasher();
    w.AddDtgt();
    w.Load();
    w.Wash();
    w.Unload();
}

method Test3()
{
    var w := new Dishwasher();
    w.Load();
    w.AddDtgt();
    w.Wash();
    w.AddDtgt();
    w.Unload();
    w.Load();
    w.Wash();
    w.Unload();
}

method Test4()
{
    var w := new Dishwasher();
    w.Load();
    w.AddDtgt();
    w.Wash();
    w.AddDtgt();
    w.Wash();
    w.Unload();
}

method Test5()
{
    var w := new Dishwasher();
    w.Load();
    w.Load();
    w.Load();
    w.AddDtgt();
    w.AddDtgt();
    w.Wash();
    w.Unload();
}


// method BadTest1()
// {
//     // wash before adding detergented
//     var w := new Dishwasher();
//     w.Load();
//     w.Wash();
// }

// method BadTest2()
// {
//     // wash before adding detergented
//     var w := new Dishwasher();
//     // forget to load dishes 
//     w.AddDtgt();
//     w.Wash();
// }

// method BadTest3()
// {
//     // wash before adding detergented
//     var w := new Dishwasher();
//     // nothing to unload 
//     w.Unload();
// }

