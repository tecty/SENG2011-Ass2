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

// predicate unShifted(a:array<int>, a_old:seq<int>, low:int, high:int)
//     reads a 
//     requires a.Length == |a_old|
//     requires 0<= low <= high  < a.Length
// {
//     // unshifted should be all the same 
//     (forall i:: (low <= i < high) ==> a[i] == a_old[i] ) &&
//     // use this for all we can show that the mulitset of these tow things are same 
//     multiset(a[low..high]) == multiset(a_old[low..high])
// }

// predicate Shifted(a:array<int>, a_old:seq<int>, low:int, high:int)
//     reads a 
//     requires a.Length == |a_old|
//     requires 0< low <= high  <= a.Length
// {
//     // define of shuffle 
//     (forall i ::  (low <= i < high )==> a[i] == a_old[i-1]) && 
//     // proof both part are same 
//     a[low .. high] == a_old[low-1..high-1] && 
//     // proof the multiset 
//     multiset(a[low .. high]) == multiset(a_old[low-1..high-1])
// }



method InsertionSortShuffle(a: array<int>)
requires a.Length>1
ensures Sorted(a, 0, a.Length);
ensures multiset(a[..]) == multiset(old(a[..]));
modifies a;
{
    var up:=1;
    var injectValue:= a[up];
    var injectPoint:= up;
    while (up < a.Length  )
        decreases a.Length - up 
        invariant 1 <= up <= a.Length;
        invariant Sorted(a, 0, up);
        invariant multiset(a[..]) == multiset(old(a[..]));
        // definition of hte inject point and value 
        invariant 0 <= injectPoint < a.Length;
        invariant injectValue == old(a)[injectPoint];
    {
        injectValue := a[up];
        injectPoint := up;

        while ( injectPoint>= 1 &&  a[injectPoint - 1] > injectValue)
            decreases injectPoint;
            invariant SortedExcept(a,0, up, injectPoint)
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
