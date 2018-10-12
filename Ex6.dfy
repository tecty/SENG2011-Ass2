predicate Sorted(a:array<int>, low:int, high:int) 
    reads a 
    // index must not out of bound 
    requires 0<= low <= high  <= a.Length
{
    forall j,k:: 0<=j<k<high ==> a[j]<=a[k] 
}

predicate SortedExcept(a:array<int>,low:int, high:int, except:int )
    reads a 
    requires 0<= low <= high  <= a.Length
    requires low <= except <= high
{
    forall j,k:: (0<=j<k<high && j != except && k != except) ==> a[j]<=a[k] 
}

predicate Shifted(a:array<int>, a_old:seq<int>, low:int, high:int)
    reads a 
    requires a.Length == |a_old|
    requires 0< low <= high  <= a.Length
{
    // define of shuffle 
    (forall i ::  (low <= i < high )==> a[i] == a_old[i-1]) && 
    // proof both part are same 
    a[low .. high] == a_old[low-1..high-1] && 
    // proof the multiset 
    multiset(a[low .. high]) == multiset(a_old[low-1..high-1])
}

predicate unShifted(a:array<int>, a_old:seq<int>, low:int, high:int)
    reads a 
    requires a.Length == |a_old|
    requires 0<= low <= high  < a.Length
{
    // unshifted should be all the same 
    (forall i:: (low <= i < high) ==> a[i] == a_old[i] ) &&
    // use this for all we can show that the mulitset of these tow things are same 
    multiset(a[0..high]) == multiset(a_old[low..high])
}




method InsertionSortShuffle(a: array<int>)

requires a.Length>1
ensures Sorted(a, 0, a.Length);
ensures multiset(a[..]) == multiset(old(a[..]));
modifies a;
{
    var up:=1;
    while (up < a.Length)
        decreases a.Length - up 
        invariant 1 <= up <= a.Length;
        invariant Sorted(a, 0, up);
        invariant multiset(a[..]) == multiset(old(a[..]));
    {
        var injectValue := a[up];
        var injectPoint := up;
        ghost var  a_old := a[..];

        while ( injectPoint>= 1 &&  a[injectPoint - 1] > injectValue)
            decreases injectPoint;
            invariant SortedExcept(a,0, up, injectPoint)
            // defined the shift and unshifted part 
            invariant unShifted(a, a_old, 0, injectPoint);
            invariant Shifted(a, a_old, injectPoint+1, up+1);
            // define of inject value 
            invariant injectValue == a_old[up];
            // first proof of content isn't changed 
            invariant multiset(a[injectPoint + 1 .. up+1])+multiset({injectValue}) == multiset(a_old[injectPoint..up+1]);

        {
            a[injectPoint] := a[injectPoint -1];
            injectPoint := injectPoint -1;
        }

        a[injectPoint] :=  injectValue;
        up:=up+1;
    }
}
method Main()
{
// do not change this code
var a := new int[][6,2,0,6,3,5,0,4,1,6,0]; // testcase 1
var msa := multiset(a[..]);
InsertionSortShuffle(a);
assert Sorted(a, 0, a.Length);
var msa_post := multiset(a[..]);
assert msa==msa_post;
var b := new int[][8,7]; // testcase 2
InsertionSortShuffle(b);
print a[..], b[..];
}
