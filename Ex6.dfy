predicate Sorted(a:array<int>, low:int, high:int) 
    reads a 
    // index must not out of bound 
    requires 0<= low <= high  <= a.Length
{
    forall j,k:: 0<=j<k<high ==> a[j]<=a[k] 
}

predicate SortedExcept(a:array<int>, high:int, except:int )
    reads a 
    requires 0<= except <= high  <= a.Length
{
    forall j,k:: (0<=j<k<high && j != except && k != except) ==> a[j]<=a[k] 
}

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
        invariant 0<= injectPoint <= up 
        invariant Sorted(a, 0, up);
        invariant multiset(a[..]) == multiset(old(a[..]));
        // invariant forall injectPoint < i <= up 
    {
        injectValue := a[up];
        injectPoint := up;
        while (injectPoint >= 1 && a[injectPoint-1] > injectValue)
            decreases injectPoint
            // invariant 0 <= up < a.Length
            invariant 0 <= injectPoint <= up;
            invariant SortedExcept(a, up +1 , injectPoint)
            // all the part at the right is bigger than inject value 
            invariant forall i :: injectPoint <= i <= up ==>  injectValue <= a[i] 
            // the data will be persist
            invariant multiset(a[..]) == multiset(old(a[..])) + multiset{a[injectPoint]} - multiset{injectValue}
        {
            a[injectPoint] := a[injectPoint-1];
            injectPoint:=injectPoint-1;
        }
        // Shifted(a, old(a),up, injectPoint);
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
