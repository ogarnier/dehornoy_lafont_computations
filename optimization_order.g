#In order to work, the script needs 
#	-the list "atoms" of atoms with some fixed target
#	-the list "simples" of simples with some fixed target
#	-a function "lcm(a,b)" wich computes the left-lcm of two atoms a and b.
#	-a function "right-div(a,b)" which checks whether or not the atom a right-divides the simple b


#--------------------------------------
Al:=function(l)#computes the atoms which right divide some simple element l
	return Filtered(atoms,a->rightdiv(a,l));
end;

nal:=function(a,l)#computes the function n(a,l) with a right-dividing l.
	return Number(Al(l),b->lcm(a,b)=l);
end;

MinNal:=function(l)#useful for computing the bounds of Lemma 2.17
	return Minimum(List(Al(l),a->nal(a,l)));
end;
MaxNal:=function(l)
	return Maximum(List(Al(l),a->nal(a,l)));
end;



#----------------------------------------
#The transitive closure of the union of a set C of conditions is not antisymetric if and only if there is a strictly increasing chain a1<a2<...<a1 of length 2 or more.
#Furthermore, we only need to care about the transitive closure of the set of chains a<b such that there is a condition [b,l] in C (only such chains can be then be prolonged into a possible contradiction)

two_cond_compat:=function(c1,c2)#tests the compatibility of two conditions (faster than with an arbitrary list)
	return c1<>c2 and (c1[1]=c2[1] or not(c1[1] in Al(c2[2]) and c2[1] in Al(c1[2])));
end;

2chains:=function(C)#C is a set of conditions, construct the set of couples [a,b] (with a<>b) induced by C such that there are conditions (a,l), (a,l') in C
	local minima,2ch;
	minima:=List(C,l->l[1]);#all minima of the conditions
	2ch:=Set(Concatenation(List(C,c->List(Filtered(Al(c[2]),b-> b in minima),b->[c[1],b]))));
	return Filtered(2ch,l->l[1]<>l[2]);
end;


longerchains:=function(chains,R)#if chains is a list of chains a1<a2<...<an, and R is a set of couples [x,y], constructs all chains a1<a2<...<an<an+1 where [an,an+1] lies in R
	return Concatenation(List(chains,c->List(Filtered(R,r->r[1]=c),r->Concatenation(c,[r[2]]))));
end;

list_cond_compat:=function(C)#tests the compatibility of a list of (more than two) conditions
	local 2ch,l;
	2ch:=2chains(C);
	l:=2chains(C);
	while l<>[] do
		l:=longerchains(2ch,2ch);
		if ForAny(l,c->c[1]=c[Length(c)]) then return false;fi;
	od;
	return true;
end;



#-------------------------------------------
L:=Set(List(Combinations(atoms,2),l->lcm(l[1],l[2])));;#Computes the lcms of all possible pairs of atoms, and return it as a set.
LL:=Filtered(L,l->MinNal(l)<>MaxNal(l));

posscond:=Concatenation(List(LL,l->List(Al(l),a->[a,l])));#If n(a,l) is the same for every a right-dividing some l, conditions of the form [a,l] cannot change the number of 2-cells, so we remove them.
SortBy(posscond,l->nal(l[1],l[2])-MinNal(l[2]));#We sort conditions according to step 3 of our procedure.
selectcond:=[posscond[1]];#the list of conditions we selected.

while posscond<>[] do
	posscond:=Filtered(posscond,c->ForAll(selectcond,d->two_cond_compat(c,d)));#We want only conditions which are pairwise compatible with all already selected conditions.
	te:=false;
	while not(te) and posscond<>[] do
		if list_cond_compat(Concatenation(selectcond,[posscond[1]])) then#checks if the next possible conditions is compatible with already selected conditions.
			Add(selectcond,posscond[1]);
			te:=true;
		fi;
		posscond:=posscond{[2..Length(posscond)]};
	od;
od;

#selectcond is now a maximal family of compatible conditions.



#-------------------------------------
NumberOf2cells:=function(selectcond)#Computes the number of 2-cells associated to the set selectcond.
	return Sum(List(Filtered(L,l->MinNal(l)=MaxNal(l)),l->MinNal(l)))+Sum(List(selectcond,l->nal(l[1],l[2])));
end;