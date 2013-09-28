% Wojciech Chmiel 305187 - rozwiazanie III zadania zaliczeniowego, wersja prostsza
% Poniewaz pisalem to rozwiazanie pozno, czasami mogla mnie poniesc ulanska
% fantazja przy nazywaniu termow i relacji. Z gory przepraszam.
% Bazowalem w swoim rozwiazniu na opisie budowy automatu z wikipedii: 
% http://pl.wikipedia.org/wiki/Generowanie_parserów_LR

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%      BUDOWANIE TABELI LR0
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

createLR0(Gramatyka, Automat, Info) :-
    stworz_wszystkie_sytuacje(Gramatyka, _, GTTab, ActionTab, Info),
    ponumeruj_gramatyke(Gramatyka, 1, Ponumerowana),
    createLR0Helper(automat(Ponumerowana, GTTab, ActionTab), Automat, Info), !.

createLR0Helper(Automat, Automat, ok).
createLR0Helper(_, null, konflikt(_)).

accept(Automat, Slowo) :-
    append(Slowo, [#], Poprawione), 
    zapusc(Automat, [0], Poprawione), !.
    
% zapuszcza automat na slowie
zapusc(automat(_, _, ActionTab), [Stan | _], [Znak | _]) :-
    member(action(Stan, _, Znak, akceptuj), ActionTab), !.
    
% redukcja, usuwamy tyle ze stosu ile nieterminali w regule
zapusc(automat(Gram, GoToTab, ActionTab), [Stan | T], Slowo) :-
    member(action(Stan, Gram_Nr, _, redukcja), ActionTab), %!,
    %write('Redukcja: '), write(Gram_Nr), nl,
    daj_produkcje(Gram, Gram_Nr, Sym, Prod),
    length(Prod, Prod_len), length(X, Prod_len), 
    % usun pierwsze Prod_len elmentow
    append(X, [Aktualny_Stan | NowyStos], [Stan | T]),
    member(goto(Aktualny_Stan, Do_dodania, nt(Sym)), GoToTab),
    !,
    zapusc(automat(Gram, GoToTab, ActionTab), [Do_dodania, Aktualny_Stan | NowyStos], Slowo), !.

% shift idze po znaku
zapusc(automat(Gram, GoToTab, ActionTab), [Stan | T], [Znak | Slowo]) :-
    member(action(Stan, Destination, Znak, shift), ActionTab), 
    !,
    %write('Shift: '), write(Destination), nl, !,
    zapusc(automat(Gram, GoToTab, ActionTab), [Destination,Stan | T], Slowo), !.

 
    
% stworz_wszystkie_sytuacje(Gramatyka, -Sytuacje, -GoTo) :-
stworz_wszystkie_sytuacje(Gramatyka, Sytuacje, TabGT, Tabela, Komunikat) :-
    alfabet(Gramatyka, Alfabet), Gramatyka = [prod(X, _) | _],
    % stworz sytuacje 0
    domkniecie( [prod('Z', [[#, nt(X)]])], Gramatyka, S0_P),
    %write('S0_P = '),write(S0_P), nl, write('Alfabet = '), write(Alfabet), nl,
    sprobuj_przejsc(S0_P, 0,Gramatyka, Alfabet, [sytuacja(0, S0_P)],Sytuacje, GoTo),
    ponumeruj_gramatyke([prod('Z', [[nt(X)]]) | Gramatyka], 0, Ponumerowana_Gram),
    tabela_gt(GoTo, TabGT),
    tabela_action(Ponumerowana_Gram, Sytuacje, GoTo, Tabela, Komunikat).

sprobuj_przejsc(Prod_Sytuacji, Nr, G, Alf, SytA, Syt, Gt) :- sprobuj_przejsc(Prod_Sytuacji, Nr, G, Alf, SytA, Syt, [], Gt).
% sprobuj przjesc - tworzy nowe sytuacje i goto, ma dwa akumulatory do tego
sprobuj_przejsc(Prod_Sytuacji, Nr, G, Alf, SytA, Syt, GtA, Gt) :-
    dodaj_sytuacje(Prod_Sytuacji, Nr, G, Alf, SytA, Syt, GtA, Gt).

dodaj_sytuacje(_, _, _, [], Syt, Syt, Gt, Gt).
% znalazlem stara sytuacje
dodaj_sytuacje(Prod_Sytuacji, Nr, G, [Znak | Alf], SytA, Syt, GtA, Gt) :-
    daj_przejscia(Prod_Sytuacji, Znak, Zalazek_Syt),
    \+ Zalazek_Syt = [],
    domkniecie(Zalazek_Syt, G, Dojrz_Syt),
    nalezy(Dojrz_Syt, SytA, Nr_stary), !,
    dodaj_sytuacje(Prod_Sytuacji, Nr, G, Alf, SytA, Syt, [goto(Nr,Nr_stary, Znak) | GtA], Gt), !.

% nowa sytuacja
dodaj_sytuacje(Prod_Sytuacji, Nr, G, [Znak | Alf], SytA, Syt, GtA, Gt) :-
    daj_przejscia(Prod_Sytuacji, Znak, Zalazek_Syt),
    \+ Zalazek_Syt = [],
    domkniecie(Zalazek_Syt, G, Dojrz_Syt), 
    SytA = [sytuacja(Max_Nr, _) | _],
    alfabet(G, SwiezyAlf),
    NowyNr is Max_Nr + 1, !,
    %write('Nowy nr: '), write(NowyNr), nl,
    dodaj_sytuacje(Dojrz_Syt, NowyNr, G, SwiezyAlf, [sytuacja(NowyNr, Dojrz_Syt) | SytA], SytA2, [goto(Nr, NowyNr, Znak) | GtA], GtA2),
    dodaj_sytuacje(Prod_Sytuacji, Nr, G, Alf, SytA2, Syt, GtA2, Gt).

% nic nie dodaje
dodaj_sytuacje(Prod_Sytuacji, Nr, G, [_ | Alf], SytA, Syt, GtA, Gt) :-
    dodaj_sytuacje(Prod_Sytuacji, Nr, G, Alf, SytA, Syt, GtA, Gt).


domkniecie(S1, G, S2) :- domkniecie(S1, G, [], nie, S2).
domkniecie([], G, Przetworzona_S, tak, W) :- domkniecie(Przetworzona_S, G, [], nie, W), !.
domkniecie([], _, Przetworzona_S, nie, Przetworzona_S) :- !.
domkniecie([prod(_, []) | Reguly], G, Przetworzona_S, Czy_Zm, W) :- domkniecie(Reguly, G, Przetworzona_S, Czy_Zm, W), !.


% hasz musi byc w kazdej produkcji
domkniecie( [prod(X, Produkcje) | Reguly], G, Przetworzona_S, _, W) :-
    nt_po_haszu(Produkcje, NTs),
    uniq(NTs, Uniq_NTs),
    %write('Wez po haszu: '), write(Uniq_NTs), nl,
    wyciagKilka(Uniq_NTs, G, U_Produkcje_NT),
    polaczTakNie([prod(X, Produkcje) | Reguly], Przetworzona_S, Cala_S, _),
    polaczTakNie(U_Produkcje_NT, Cala_S , Polaczone_Prod, CzyZmienione),
    domkniecie(Reguly, G, Polaczone_Prod, CzyZmienione, W).


% skopiuj goto dla nieterminali dla nieterminali
tabela_gt(GT, Tabela) :- tabela_gt(GT, [], Tabela).
tabela_gt([], Tabela, Tabela).
tabela_gt([goto(X, Y, nt(Z)) | GT], A, Tabela) :- tabela_gt(GT, [goto(X, Y, nt(Z)) | A], Tabela), !.
% dla terminala
tabela_gt([_ | GT], A, Tabela) :- tabela_gt(GT, A, Tabela).


%tabela_action
tabela_action(Ponumerowana_Gram, Sytuacje, GT, Tabela, Komunikat) :- %:- tabela_action(Ponumerowana_Gram, Sytuacje, GT, [], Tabela).
    dodaj_shifty(GT, Tab_shifts),
    Ponumerowana_Gram = [R0 | Reszta_Gramatyki],
    R0 = prod(_, [reg(_, Pierwsza_regula)]),
    append(Pierwsza_regula, [#], Do_Accepta),
    nr_sytuacji(Sytuacje, Do_Accepta, Nr_Acc),
    % dodaj action(Nr_acc, nie_interesuj_sie, #, accept),
    %dodaj_redukcje(Ponumerowana_Gram
    terminale(GT, Terminale),
    % wrzucamy od reszty_gramatyki, bo nie ma redukcji dla R0
    dodaj_redukcje([# | Terminale], Reszta_Gramatyki, Sytuacje, [action(Nr_Acc, nie_interesuj_sie, #, akceptuj) | Tab_shifts],
                    Tabela, Komunikat).

    
% dodaj shifty do tabeli parsingu
dodaj_shifty(GT, Tab) :- dodaj_shifty(GT, [], Tab).
dodaj_shifty([], Tab, Tab).
dodaj_shifty([goto(_, _, nt(_)) | GT], A, Tab) :- dodaj_shifty(GT, A, Tab), !.
dodaj_shifty([goto(From, To, Terminal) | GT], A, Tab) :- dodaj_shifty(GT, [action(From, To, Terminal, shift) | A], Tab).


% na Nr zostaje przypisany nr sytuacji zawirajacej Szukana produkcje
nr_sytuacji([sytuacja(Nr, Produkcje) | _], Szukana, Nr) :- w_produkcjach(Szukana, Produkcje), !.
nr_sytuacji([_ | S], Prod, Nr) :- nr_sytuacji(S, Prod, Nr).


% daj_produkcje o nr
daj_produkcje([prod(S, [reg(Nr, P) | _]) | _], Nr, S, P) :- !.
daj_produkcje([prod(_, []) | Reguly], Nr, S, P) :- daj_produkcje(Reguly, Nr, S, P), !.
daj_produkcje([prod(_, [_ | Produkcje]) | Reguly], Nr, S, P) :- daj_produkcje([prod(S, Produkcje) | Reguly], Nr, S, P).


% True jesli szukana produkcja jest w zbiorze produkcji
w_produkcjach(Szukana, [prod(_, P) | _]) :- member(Szukana, P), !.
w_produkcjach(Szukana, [_ | P]) :- w_produkcjach(Szukana, P).


% daje zbior terminali uzytych w gramatyce
terminale(GT, Ts) :- terminale(GT, [], Ts).
terminale([], Ts, U_Ts) :- uniq(Ts, U_Ts).
terminale([goto(_, _, nt(_)) | GT], A, Ts) :- terminale(GT, A, Ts), !.
terminale([goto(_, _, T) | GT], A, Ts) :- terminale(GT, [T | A], Ts).


% dodaje redukcje do tabeli parsingu, zwraca komuniaty o bledach gramatyki.
dodaj_redukcje(Terminale, Ponumerowana_Gram, Sytuacje, Tabela, WynTab, Komunikat) :-
    dodaj_redukcje(Terminale, Ponumerowana_Gram, Sytuacje, Tabela, [], WynTab, Komunikat), !.
dodaj_redukcje(_, [], _, _, WynTab, WynTab, ok).
dodaj_redukcje(Terminale, [prod(_, []) | R], Sytuacje, Tabela, A, WynTab, Komunikat) :-
    dodaj_redukcje(Terminale, R, Sytuacje, Tabela, A, WynTab, Komunikat), !.
dodaj_redukcje(Terminale, [prod(S, [P | Produkcje]) | Reguly], Sytuacje, Tabela, A, WynTab, Komunikat) :-
    P = reg(Reg_nr, Reg_body),
    append(Reg_body, [#], Pszarp),
    nr_sytuacji(Sytuacje, Pszarp, Nr),
    generuj_redukcje(Terminale, Nr, Reg_nr, Redukcje),
    uniq(Redukcje, UniqRedukcje),
    zmerdzuj_redukcje(UniqRedukcje, Tabela, Cz_WynTab, Cz_Komunikat),
    append(Cz_WynTab, A, Nowy_Lepszy_Akumulator),
    decyzja(Cz_Komunikat, Terminale, [prod(S, Produkcje) | Reguly], Sytuacje, Tabela, Nowy_Lepszy_Akumulator, WynTab, Komunikat), !.

decyzja( konflikt(X), _, _, _, _, _, null, konflikt(X)).
decyzja( _, Terminale, Gram, Sytuacje, Tabela, A, WynTab, Komunikat) :- uniq(A, UniqA),
    dodaj_redukcje(Terminale, Gram, Sytuacje, Tabela, UniqA, WynTab, Komunikat), !.


generuj_redukcje(Ts, N1, N2, R) :- generuj_redukcje(Ts, N1, N2, [], R).
generuj_redukcje([], _, _, Redukcje, Redukcje).
generuj_redukcje([T | Terminale], N1, N2, A, R) :- generuj_redukcje(Terminale, N1, N2, [action(N1, N2, T, redukcja) | A], R).


zmerdzuj_redukcje(Redukcje, Tabela, WynTab, Komunikat) :- zmerdzuj_redukcje(Redukcje, Tabela, [], WynTab, Komunikat).
zmerdzuj_redukcje([], Tabela, A, WynTab, ok) :- append(Tabela, A, WynTab).
zmerdzuj_redukcje([action(N1, _, Zn, redukcja) | Akcje ], _, _, null, konflikt('Redukcja-Redukcja')) :- member(action(N1, _, Zn, redukcja), Akcje), !.
zmerdzuj_redukcje([action(N1, _, Zn, redukcja) | _], Tabela, _, null, konflikt('Redukcja-Przesuniecie')) :- member(action(N1, _, Zn, shift), Tabela), !.
zmerdzuj_redukcje([Ak | Aks], Tabela, A, WynTab, Kom) :- zmerdzuj_redukcje(Aks, Tabela, [Ak | A], WynTab, Kom).


% daje produkcje, jakie mozemy otrzymac po przejsciu znaku Znak
daj_przejscia(Prod_Sytuacji, Znak, Nowa) :- daj_przejscia(Prod_Sytuacji, Znak, [], [], Nowa), !.
daj_przejscia( [], _, _, Nowa, Nowa).
daj_przejscia( [prod(_, []) | Reguly], Znak, [], A, W) :- daj_przejscia(Reguly, Znak, [], A, W), !.
daj_przejscia( [prod(X, []) | Reguly], Znak, RevProdA, A, W) :- rev(RevProdA, ProdA), daj_przejscia(Reguly, Znak, [], [prod(X, ProdA) | A], W), !.
daj_przejscia( [prod(X, [P | Produkcje]) | Reguly], Znak, RevProdA, A, W) :-
    wez_po_haszu(P, Znak), % dopasowanie do Znaku
    !,
    przesun_hasz(P, Przesuniete_P),
    daj_przejscia([prod(X, Produkcje) | Reguly], Znak, [Przesuniete_P | RevProdA], A, W).
% nie dopasowalismy znaku
daj_przejscia( [prod(X, [_ | Produkcje]) | Reguly], Znak, RevProdA, A, W) :-
    daj_przejscia([prod(X, Produkcje) | Reguly], Znak, RevProdA, A, W), !.

liczba_nt(Prod, X) :- liczba_nt(Prod, 0, X).
liczba_nt([], X, X).
liczba_nt([nt(_) | P], A, X) :- NoweA is A + 1, liczba_nt(P, NoweA, X), !.
liczba_nt([_ | P], A, X) :- liczba_nt(P, A, X).

ponumeruj_gramatyke(G, Nr, Nowa_G) :- ponumeruj_gramatyke(G, Nr, [], Nowa_G).
ponumeruj_gramatyke([], _, RevW, W) :- rev(RevW, W).
ponumeruj_gramatyke([prod(X, Prod) | Reguly], Nr, A, W) :- 
    ponumeruj_reguly(Prod, Nr, NowyProd, NowyNr),
    ponumeruj_gramatyke(Reguly, NowyNr, [prod(X, NowyProd) | A], W).

ponumeruj_reguly(P, Nr, NowyProd, NowyNr) :- ponumeruj_reguly(P, Nr, [], NowyProd, NowyNr).
ponumeruj_reguly([], Nr, A, NowyProd, Nr) :- rev(A, NowyProd).
ponumeruj_reguly([P | Prod], Nr, A, NowyProd, NowyNr) :- 
    Nast is Nr + 1, 
    ponumeruj_reguly(Prod, Nast, [reg(Nr, P) | A], NowyProd, NowyNr).


% daj alfabet znakow w gramatyce
alfabet(G, A) :- alfabet(G, [], A).
alfabet([], A, U_A) :- uniq(A, U_A).
alfabet([prod(S, P) | Reguly], A, W) :-
    znaki_z_produkcji(P, Z),
    append([nt(S) | Z], A, Nowy_Lepszy_Akumulator),
    alfabet(Reguly, Nowy_Lepszy_Akumulator, W).

% daj alfabet z produkcji jednego nt
znaki_z_produkcji(L, Alfa) :- znaki_z_produkcji(L, [], Alfa).
znaki_z_produkcji([], A, U_A) :- uniq(A, U_A).
znaki_z_produkcji([H1| T], A, W) :- 
    append(H1, A, Nowy_Lepszy_Akumulator),
    znaki_z_produkcji(T, Nowy_Lepszy_Akumulator, W).
   

% dodaj hasze na poczatek
dodaj_hasze(Produkcje, Ulepszone) :- dodaj_hasze(Produkcje, [], Ulepszone).
dodaj_hasze([], U, U).
dodaj_hasze([[]], U, [[#] | U]).
dodaj_hasze([ [# | T] | Produkcje], A, U) :- dodaj_hasze(Produkcje, [[# | T] | A], U).
dodaj_hasze([ [H | T] | Produkcje], A, U) :- dodaj_hasze(Produkcje, [[#, H | T] | A], U).
   

% wez pierwsze znaki po haszu z wszystkich produkcji
nt_po_haszu(P, NTs) :- nt_po_haszu(P, [], NTs).
nt_po_haszu([], NTs, NTs).
nt_po_haszu([P | T], A, NTs) :- wez_po_haszu(P, nt(NT)), nt_po_haszu(T, [NT | A], NTs), !.
nt_po_haszu([_ | T], A, NTs) :- nt_po_haszu(T, A, NTs).


% wez pierwszy znak po haszu
wez_po_haszu([#, H | _], H).
wez_po_haszu([_ | T], W) :- wez_po_haszu(T, W).


% przesun hasz o 1
przesun_hasz(L, W) :- przesun_hasz(L, [], W).
przesun_hasz([#, H | T], A, W) :- rev(A, RevA), append(RevA, [H, # | T], W), !.
% jesli hasz jest ostatni
przesun_hasz([# | T], A, W) :- T = [], rev([# | A], W).
% jesli nie hasz
przesun_hasz([H | T], A, W) :-  przesun_hasz(T, [H | A], W).


% wyciagnij produkcje nieterminali NTs i dodaj hasze na poczatek
wyciagKilka(NTs, G, Produkcje_NTs) :- wyciagKilka(NTs, G, [], Produkcje_NTs).
wyciagKilka([], _, Produkcje_NTs, Produkcje_NTs).
wyciagKilka([NT | Reszta_NT], G, A, W) :- 
    wyciag(G, NT, Produkcja_NT),
    dodaj_hasze(Produkcja_NT, Ulepszona_P),
    wyciagKilka(Reszta_NT, G, [prod(NT, Ulepszona_P) | A], W). 


% zakladam ta sama kolenosc produkcji w danej regule
polaczTakNie(Xs, Ys, W, Dec) :- polaczTakNie(Xs, Ys, [], W, nie, Dec).
polaczTakNie([], Ys, A, W, DecA, DecA) :- append(Ys, A, W).
polaczTakNie([H | T], Ys, A, W, DecA, Dec) :- member(H, Ys), !, polaczTakNie(T, Ys, A, W, DecA, Dec).
% nie prawda ze member
polaczTakNie([H | T], Ys, A, W, _, Dec) :- polaczTakNie(T, Ys, [H | A], W, tak, Dec).


uniq(L, UL) :- uniq(L, [], UL).
uniq([], UL, UL).
uniq([H | L], A, UL) :- member(H, L), uniq(L, A, UL), !.
uniq([H | L], A, UL) :- uniq(L, [H | A], UL).


% Sprawdza czy jakas sytuacja jest identyczna z ktoras ze zbioru
nalezy(Syt, [Syt1 | _], Nr) :- identS(Syt, Syt1), !, Syt1 = sytuacja(Nr, _).
nalezy(Syt, [_ | ZbiorSyt], Nr) :- nalezy(Syt, ZbiorSyt, Nr).

identS(ProdukcjeSyt, sytuacja(_, ProdukcjeSyt1)) :- polaczTakNie(ProdukcjeSyt, ProdukcjeSyt1, ProdukcjeSyt1, nie).

rev(L, R) :- rev(L, [], R).
rev([],A,A).
rev([H|T],A,R):-  rev(T,[H|A],R). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%       First & Follow
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Komentarz: Drogi Czytelniku ponizszego kodu,
% chcialem Cie przeprosic, poniewaz kod napisany ponizej jest
% watpliwej jakosci, rzadko dziala poprawnie i jego brzydota
% razi samego autora. Na usprawiedliwnie: byl pisany w pospiechu,
% i potrzebowalem go do budowy automatu LR0.


% wyciag(Gram, Symbol, Wynik).
wyciag([prod(S, Produkcje_S) | _ ],   S, Produkcje_S).
wyciag([first(S, S_first) | _], S, S_first).
wyciag([follow(S, S_follow) | _], S, S_follow).
wyciag([ _ | X], S, W) :- wyciag(X, S, W).

polacz(Xs, Ys, W) :- polacz(Xs, Ys, [], W).
polacz([], Y, A, W) :- append(Y, A, W).
polacz([X | Xs], Ys, A, W) :- member(X, Ys), polacz(Xs, Ys,  A, W), !.
polacz([X | Xs], Ys, A, W) :- polacz(Xs, Ys, [X | A], W).


% first(+produkcje, produkcja, -przetworzone, wynik)

%first([], V, epsilon).
firsts(Gram, W) :- first_sets(Gram, [], [], W).

first_sets([], _, A, A).                                   % musza byc, bo wywolujemy rekurencyjnie na nich
first_sets([prod(S, Produkcje_S)| Reguly], Visited, A, W) :- 
            stworz_first(Produkcje_S, Reguly, [S | Visited], A, [], S_first),
            first_sets(Reguly, [S | Visited], [first(S, S_first) | A], W).


% Prawdopodbnie musisz dodac sprawdzanie A -> BCD, if B,C,D -> eps, to first(A) zawiera eps

stworz_first([], _, _, _, A, A). %:- print(' HE HE HEHESZKI\n').
stworz_first([[eps] | Produkcje], Reguly, Visited, Cz, A, Wynik) :- %print('2 - dwojka'), 
                        !, stworz_first(Produkcje, Reguly, Visited, Cz, [eps | A], Wynik).
% stworz gdzy eps w first(X)
stworz_first([[nt(X) | Reszta_Strony] | Produkcje], Reguly, Visited, Cz, A, Wynik) :- %print('3 - trojka'),
                \+ member(X, Visited), wyciag(Reguly, X, X_prawe),
                stworz_first(X_prawe, Reguly, [X | Visited], Cz, [], X_first), 
                member(eps, X_first), 
                !, polacz(X_first, A, [], X_and_A),
                stworz_first([ Reszta_Strony | Produkcje],   Reguly, Visited, Cz, X_and_A, Wynik).
% gdy eps nie w first(X)
stworz_first([[nt(X) | _ ] | Produkcje], Reguly, Visited, Cz, A, Wynik) :- %print('3 - trojka'),
                \+ member(X, Visited), wyciag(Reguly, X, X_prawe),
                stworz_first(X_prawe, Reguly, [X | Visited], Cz, [], X_first), 
                !, polacz(X_first, A, [], X_and_A),
                stworz_first(Produkcje,   Reguly, Visited, Cz, X_and_A, Wynik).
% gdy first(X) juz obliczone
stworz_first([[nt(X) | Reszta_Strony ] | Produkcje], Reguly, Visited, Cz, A, Wynik) :-  %print('4 - czworka'),
                member(X, Visited), wyciag(Cz, X, X_first), !,
                stworz_first([ Reszta_Strony | Produkcje],   Reguly, Visited, Cz, [X_first | A], Wynik).
% gdy X jest terminalem
stworz_first([[X | _] | Produkcje], Reguly, Visited, Cz, A, Wynik) :- %print('Hej ho'), 
                    atom(X), !,
                    stworz_first(Produkcje, Reguly, Visited, Cz, [X | A], Wynik).

stworz_first([[] | Produkcje], Reguly, Visited, Cz, A, Wynik) :- %print('Wchodze do dziwaka'),
        stworz_first(Produkcje, Reguly, Visited, Cz, A, Wynik).


% tylko do follow
zmerdzuj(Follows, S_follow, W) :- zmerdzuj(Follows, S_follow, [], W).
zmerdzuj(Follows, follow(_, []), _, Follows).
zmerdzuj([],S, W, [S | W]).
zmerdzuj([follow(S, L) | Fs], follow(S, Prawa), A, [follow(S, Wyn) | Niezmienione]) :- 
                polacz(L, Prawa, [], Wyn), append(Fs, A, Niezmienione), !.
zmerdzuj([follow(S1, L) | Fs], follow(S2, Prawa), A, W) :- zmerdzuj(Fs, follow(S2, Prawa), [follow(S1, L) | A], W).


follows([prod(S, R) | P], W) :- G = [prod(S, R) | P], follow_set(G, G, [follow(S, [#])], Z), follow_set(G, G, Z, W).

% rule0 -> dodaj # do startowego
% rule1 -> A -> aBc, to follow(B) u= first(c) \ eps
% rule2 -> 

follow_set([], _, W, W).
% move to the next non-terminal
follow_set([prod(_, []) | Reguly], Gram, Akum, Wyn) :- follow_set(Reguly, Gram, Akum, Wyn), !.
% move to the next production
follow_set([prod(X, [[] | Rs]) | Reguly], Gram, Akum, Wyn) :- follow_set([prod(X, Rs) | Reguly], Gram, Akum, Wyn), !.
follow_set([prod(X, [[_] | ProdukcjeX]) | Reguly], Gram, Akum, Wyn) :- print('3\n'),follow_set([prod(X, [ProdukcjeX]) | Reguly], Gram, Akum, Wyn), !.

% epsilon w first(c)
follow_set([prod(X, [[nt(NT) | OgonProd] | ProdukcjeX]) | Reguly], Gram, Akum, Wyn) :- 
    \+ OgonProd = [], %//wez_firsty(OgonProd, Ogon_first), 
    stworz_first([OgonProd], Gram, [], [], [], Ogon_first), 
    delete(Ogon_first, eps, Ogon_bez_eps), % dodaj do akuma NT -> Ogon_bez_eps
    \+ Ogon_first = Ogon_bez_eps, !,
    wyciag(Akum, X, X_follow),
    zmerdzuj(Akum, follow(NT, Ogon_bez_eps), Akum1),
    zmerdzuj(Akum1, follow(NT, X_follow), Akum_final),
    follow_set([prod(X, [OgonProd | ProdukcjeX]) | Reguly], Gram, Akum_final, Wyn).


% brak epsilon w first(c)
follow_set([prod(X, [[nt(NT) | OgonProd] | ProdukcjeX]) | Reguly], Gram, Akum, Wyn) :- 
    \+ OgonProd = [], %//wez_firsty(OgonProd, Ogon_first), 
    stworz_first([OgonProd], Gram, [], [], [], Ogon_first), 
    \+ member(Ogon_first, eps), !,
    zmerdzuj(Akum, follow(NT, Ogon_first), Akum_final),
    follow_set([prod(X, [OgonProd | ProdukcjeX]) | Reguly], Gram, Akum_final, Wyn).

% NT -> aB
follow_set([prod(X, [[nt(NT) | OgonProd] | ProdukcjeX]) | Reguly], Gram, Akum, Wyn) :- 
    OgonProd = [], !, %//wez_firsty(OgonProd, Ogon_first), 
    wyciag(Akum, X, X_follow),
    zmerdzuj(Akum, follow(NT, X_follow), Akum_final),
    follow_set([prod(X, [OgonProd | ProdukcjeX]) | Reguly], Gram, Akum_final, Wyn).

follow_set([prod(X, [[_ | OgonProd] | ProdukcjeX]) | Reguly], Gram, Akum, Wyn) :- 
    follow_set([prod(X, [OgonProd | ProdukcjeX]) | Reguly], Gram, Akum, Wyn).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%           Testy
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% test(+NazwaGramatyki, +ListaSlowDoZbadania)
test(NG, ListaSlow) :-
     grammar(NG, G),
     createLR0(G, Automat, ok),
     checkWords(ListaSlow, Automat).

checkWords([], _) :-  write('Koniec testu.\n').
checkWords([S|RS], Automat) :-
      format("  Slowo: ~p ", [S]),
      (accept(Automat, S) -> true; write('NIE ')),
      write('nalezy.\n'),
      checkWords(RS, Automat).


grammar(ex1, [prod('E', [[nt('E'), '+', nt('T')],  [nt('T')]]),
          prod('T', [[id],  ['(', nt('E'), ')']])   ]).
grammar(ex4, [prod('A', [[x, nt('B')], [nt('B'), y], []]),
              prod('B', [[]])]).
grammar(ex5, [prod('S', [[id], [nt('V'), ':=', nt('E')]]),
              prod('V', [[id], [id, '[', nt('E'), ']']]),
              prod('E', [[nt('V')]])]).
grammar(ex6, [prod('E', [[nt('T'), nt('G')]]),
          prod('G', [[+, nt('T'), nt('G')], [eps]]),
          prod('T', [[nt('F'), nt('K')]]), 
          prod('K', [[eps], [*, nt('F'), nt('K')]]),
          prod('F', [['(', nt('E'),')'], [id]])]).
grammar(ex7, [prod('F', [['(', nt('F'),')'], [id]])]).
grammar(ex8, [prod('S', [[nt('E'), nt('Sp')]]),
          prod('Sp', [[';', nt('S')], [eps]]),
          prod('E', [['(', nt('S'), ')'], [eps]])]).
grammar(ex9, [prod('E', [[nt('E'), *, nt('B')], [nt('E'), +, nt('B')], [nt('B')]]),
          prod('B', [[0], [1]])]).



