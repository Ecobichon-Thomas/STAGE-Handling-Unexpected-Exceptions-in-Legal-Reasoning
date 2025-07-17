import pandas as pd
import numpy as np
from logic import *
from scipy.spatial import distance

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

###### GESTION DES VARIABLES #######

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

class VariableUnicity:
    def __init__(self):
        self._variables = {}

    def get(self, name):
        if name not in self._variables:
            self._variables[name] = Variable(name)
        return self._variables[name]

    def get_many(self, *names):
        return [self.get(name) for name in names]

    def __str__(self):
        variables_str = ', '.join(self._variables.keys())
        return f"Variables enregistrées: {variables_str}"
    
#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def list_to_vars(Var_dict,Str_List):                # Cette fonction permet à partir d'une liste de noms de variables (potentiellement contenant '~' comme marqueur de la négation en 1er caractère) de créer une liste de propositions
    temp = np.array(Str_List)
    negations_index = []
    for indice,t in enumerate(temp):                # On regarde toutes les variables qui ont des négations (il peut y avoir plusieurs égations ex: ~~~a)
        i = 0
        negation = False
        while i<len(t) and t[i]=='~':
            i+=1
            negation = not negation
        temp[indice] = temp[indice][i:]             # On enlève les '~' des chaînes de caractères
        if negation:
            negations_index.append(indice)                  # On note l'indice de toutes celles qui correspondent à des négations (par ex, si on a ~~a on ne compte pas a puisque les 2 negations s'annulent)

    P = np.array(Var_dict.get_many(*temp))             # Ici on check si il existe déjà des variables (négation enlevée) avec les noms donnés et on renvoie les variables correspondantes (on ajoute les variables qui n'existaient pas)
    P[negations_index] = [~s for s in P[negations_index]]               # On rajoute la négation sur les variables concernées
    
    return P.tolist()

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def negation_equivalence (Vect_premises,W):
    temp = Vect_premises.copy()
    for i,p in enumerate(Vect_premises):
        if isinstance(p,Not):

            for f in W:
                if not isinstance(f,Iff):
                    continue

                left,right = f.children
                if left.is_equivalent(p):
                    temp[i] = right
                    break               # HYPOTHESE : On a pas 2 équivalences qui s'appliquent à la mm proposition (ex: ~a<=>b et ~a<=>c)
                elif p.children[0].is_equivalent(left):
                    temp[i] = right.children[0]
                    break
                if right.is_equivalent(p):
                    temp[i] = left
                    break
                elif p.children[0].is_equivalent(right):
                    temp[i] = left.children[0]
                    break
    return temp

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def ensemble_premices_equi (premises, W):             # En recevant un vecteur de premises, renvoie toutes les prémises "impliquées" par W
    extended = list(premises.copy())
    changed = True

    while changed:              # On boucle tant que des premises sont ajoutées
        changed = False
        for f in W:
            if not isinstance(f, Iff):
                continue
            left, right = f.children

            if left in extended and right not in extended:
                extended.append(right)
                changed = True
            elif isinstance(left, Not) and left.children[0] in extended and Not(right) not in extended:
                extended.append(Not(right))
                changed = True
            elif right in extended and left not in extended:
                extended.append(left)
                changed = True
            elif isinstance(right, Not) and right.children[0] in extended and Not(left) not in extended:
                extended.append(Not(left))
                changed = True
    return extended

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#






###### RULE #######

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
class Rule:
    def __init__(self,premises, conclusion):
        # A initialiser uniquement dans une Rule_Base

        if not all(isinstance(p, Proposition) for p in premises):
            raise TypeError("premises doit être une liste de propositions")
        
        if not all(isinstance(c, Proposition) for c in conclusion):
            raise TypeError("conclusion doit être une liste de propositions")
        
        self.premises = premises   # Une liste de propositions
        self.conclusion = conclusion   # Une liste de propositions

    def __str__(self):
        premises_str = ' ^ '.join(str(p) for p in self.premises)
        conclusion_str = ' ^ '.join(str(c) for c in self.conclusion)
        return f"Rule: {premises_str} => {conclusion_str}"

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK''' 
def is_a_in_b(short, long):
    return all(any(x.is_equivalent(y) for y in long) for x in short)

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def children_extraction(formula):
    childrens = []
    temp = formula.children
    for i in temp:
        if i.children == []:
            childrens.append(i.name)
        else:
            childrens = childrens+children_extraction(i)
    return childrens

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def dictionnaire_eval_rules (Rb,rules):
    Truth_Dict = {p : False for p in Rb.Var_dictionnary._variables}              # On crée un dictionnaire avec toutes les propositions utilisées dans Rb (ne contient pas de négation par construction)
    Propositions = Rb.S
    Propositions_names = []
    for r in rules:# Liste des propositions utilisées dans S plus les conclusions des 2 règles sélectionnées
        Propositions =  Propositions + r.conclusion
    all_p = ensemble_premices_equi(Propositions, Rb.W)                # Toutes les propositions engendrées par les propositions de départ
    for s in all_p:
        for s_bis in all_p:
            if s_bis.is_equivalent(Not(s)):             # On teste si la négation de chacunes des propositions est dans le vecteur, si c'est le cas on sort immédiatement de la fonction
                return -1,[]
        if not isinstance(s,Not):
            Propositions_names.append(s.name)
            Truth_Dict[s.name] = True               # Si jamais la proposition n'est pas une négation, on fixe sa valeur à True
        else:
            Propositions_names.append(s.children[0].name)
    return Truth_Dict,Propositions_names

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def check_conflict(conclusions1, conclusions2):
    for c1 in conclusions1:
        for c2 in conclusions2:
            if Not(c1).is_equivalent(c2):
                return True
    return False

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#


###### RULEBASE #######

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK''' 
class Rule_Base:
    def __init__(self):
        self.premises = []          # Liste unique des prémisses utilisés
        self.conclusions = []           # Liste de toutes les conclusions des règles
        self.rules = []         # toutes les rules
        self.P = []         # Matrice binaire des prémisses de chaque rule
        self.C = []         # Vecteur des conclusions (Propositions)
        self.compteur = 0
        self.Var_dictionnary = VariableUnicity()                # On crée un dictionnaire de toutes les variables utilisés pour s'assurer de leur unicité
        self.W = []
        self.S = []

    def __str__(self):
        return "\n".join(str(rule) for rule in self.rules)
    
    def all_dictionnary(self):
        return self.Var_dictionnary
    
    def add_W(self,f_string_list):             # ATTENTION, IL FAUT INITIALISER W EN 1ER ET NE PLUS AJOUTER DE REGLES DEDANS                # TEST OK
        for i in f_string_list:
            f = str_to_formula(i,self)
            self.W.append(f)

    def init_S(self,list_S):                # TEST OK
        self.S = negation_equivalence (list_to_vars(self.Var_dictionnary,list_S),self.W)
        count = 0
        for s in self.S:
            if (not isinstance(s,Not)) and (s not in self.premises):
                self.premises.append(s)
                count += 1
            elif (isinstance(s,Not)) and (s.children[0] not in self.premises):
                self.premises.append(s.children[0])
                count +=1
        
        for vecteur in self.P:              # Mise à jour de la matrice P
            vecteur.extend([0] * count)

    def add_rules(self, list_P, list_C):                # TEST OK
        if self.W == []:
            raise ValueError("Il faut définir W avant d'ajouter des règles")
        if len(list_P) != len(list_C):
            raise ValueError("Nombre de listes de prémises et de conclusions incohérent.")
        for i in range(len(list_P)):
            P = negation_equivalence (list_to_vars(self.Var_dictionnary,list_P[i]),self.W)              # On élimine les négations dans tout les cas où il existe une équivalence pour ces négations dans W (ex: ~c<=>d)
            C = negation_equivalence (list_to_vars(self.Var_dictionnary,list_C[i]),self.W)

            for c in C:
                if (not isinstance(c,Not)) and (c not in self.conclusions):               # Mise à jour de self.conclusions
                    self.conclusions.append(c)
                elif (isinstance(c,Not)) and (c.children[0] not in self.conclusions):
                    self.conclusions.append(c.children[0])
                
            count = 0               # compteur du nombre de premises ajoutées
            for p in P:             # Mise à jour de self.premises
                if (not isinstance(p,Not)) and (p not in self.premises):
                    self.premises.append(p)
                    count += 1
                elif (isinstance(p,Not)) and (p.children[0] not in self.premises):
                    self.premises.append(p.children[0])
                    count +=1

            bin_vector = [1 if prem in P else -1 if Not(prem) in P else 0 for prem in self.premises]              # Création du vecteur de la nouvelle règle (1 pour la présence d'un premise, -1 pour la négation d'un premise, 0 sinon)

            for vecteur in self.P:              # Mise à jour de la matrice P
                vecteur.extend([0] * count)

            rule = Rule(P, C)               # Mise à jour des variables de la rule base
            self.rules.append(rule)
            self.P.append(bin_vector)
            self.C.append(C)
            self.compteur += 1

    #def remove_rules(self,l):              # Pas à jour et inutilisé
    #    self.rules = [v for i, v in enumerate(self.rules) if i not in l]
    #    self.C  = [v for i, v in enumerate(self.C) if i not in l]
    #    self.P  = [v for i, v in enumerate(self.P) if i not in l]
    #    self.compteur = self.compteur-1
    
    def inclusion(self, indices):                # TEST OK
        if len(indices) == 0:           # Convention: si le vecteur est vide c'est qu'on veut comparer avec toute les règles
            return [i for i in range(self.compteur) if is_a_in_b(self.rules[i].premises, self.S)]
        else:
            return [i for i in indices if is_a_in_b(self.rules[i].premises, self.S)]
        
    def compatibility_matrix(self,indices):                # TEST OK
        n = len(indices)             # indices est un vecteur des indices de toutes les règles dont on veut comparer la compatibilité
        compatibility_matrix = np.zeros((n,n))

        for a in range(n):
            for b in range(a+1, n):
                i = indices[a]
                j = indices[b]

                r1 = self.rules[i]
                r2 = self.rules[j]

                conclusions1 = r1.conclusion              # Attention, pour l'instant les conclusions sont des listes de longueur 1, il faudra changer la suite après
                conclusions2 = r2.conclusion

                if is_a_in_b(r1.premises, r2.premises):              # On teste si il y a inclusion des premises d'une règle dans l'autre
                    if check_conflict(conclusions1, conclusions2):
                        compatibility_matrix[i, j] = 1
                    else:
                        if not self.compatible([r1,r2]):
                            compatibility_matrix[i, j] = 1
                elif is_a_in_b(r2.premises, r1.premises):               # Si c'est inclus dans l'autre sens on remplit le bas de la matrice,
                    if check_conflict(conclusions1, conclusions2):
                        compatibility_matrix[j, i] = 1
                    else:
                        if not self.compatible([r1,r2]):
                            compatibility_matrix[j, i] = 1
        return compatibility_matrix
    
    def dist_hamming(self, indice):                # TEST OK
        P1 = np.atleast_2d(self.P[indice])[0]             # indice est l'indice de la règle qu'on va comparer aux autres
        C1 = self.C[indice]
        C1_full = ensemble_premices_equi (C1, self.W)
        c1_str = ' & '.join(str(p) for p in C1_full)

        C = self.C
        P = np.array(self.P)
        same_concl = []
        for c in C:
            c_full = ensemble_premices_equi (c, self.W)
            print(' & '.join(str(p) for p in c_full)+" <=> "+c1_str)
            str_formula = (' & '.join(str(p) for p in c_full)+" <=> "+c1_str)
            eq_c = str_to_formula(str_formula, self)
            if eq_c.is_tautology():
                same_concl.append(True)              # On regarde les lignes avec des conclusions identiques
            else:
                same_concl.append(False)

        n = len(self.Var_dictionnary._variables)
        dists = np.full(len(C), n + 1)             # On fixe la distance par défault à delta, si les conclusions des 2 régles sont les mêmes on modifira cette distance

        if np.any(same_concl):
            same_ccl = [i for i, x in enumerate(same_concl) if x == True]
            for i in same_ccl:
                dists[i] = distance.hamming(P1, P[i])*len(P1)               # Règles avec mm conclusion, calcul de distance de Hamming     
        return list(dists)

    def is_identical(self):                 # TEST OK
        bin_vector = [1 if prem in self.S else -1 if Not(prem) in self.S else 0 for prem in self.premises]
        try:
            return self.P.index(bin_vector)
        except ValueError:
            return -1
        
    def compatible(self,r):
        Truth_dict,propositions = dictionnaire_eval_rules (self,r)
        if Truth_dict == -1:
            return False
        W_temp = (self.W).copy()
        for w in self.W:
            if isinstance(w,Iff):
                if set(children_extraction(w)).isdisjoint(propositions):
                    W_temp.remove(w)
        return all(w.evaluate(**Truth_dict) for w in W_temp)

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#



###### SELECTION REGLES ADAPTEES ######

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def Select_Rule_web (rulebase,regles_possibles):
        C_matrix = rulebase.compatibility_matrix(regles_possibles)
        rows_to_remove = set(np.where(C_matrix == 1)[0])
        regles_possibles = [r for i, r in enumerate(regles_possibles) if i not in rows_to_remove]               # On va supprimer toutes les règles moins prioritaires
        return regles_possibles

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def select_fct_treshold (Dist_vector,threshold):
    i = Dist_vector.index(0)                # On enlève la règle qu'on compare
    Dist_vector[i] = int(threshold)+1

    D = np.array(Dist_vector)
    return np.where(D < int(threshold))[0]

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def select_fct_minimal (Dist_vector):
    i = Dist_vector.index(0)                # On enlève la règle qu'on compare
    Dist_vector[i] = max(Dist_vector)+1

    D = np.array(Dist_vector)
    return np.where(D == np.min(D))[0]

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def select_fct_treshold_minimal (Dist_vector,threshold):
    i = Dist_vector.index(0)                # On enlève la règle qu'on compare
    Dist_vector[i] = int(threshold)+1

    D = np.array(Dist_vector)
    if np.min(D)<int(threshold):
        retour = np.where(D == np.min(D))[0]
    else:
        retour = []
    return retour

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def scenario_check_web4_test(S, rulebase,deja_appliquees):
    rulebase.init_S(S)
    output = []

    regles_possibles = rulebase.inclusion([])

    temp = regles_possibles.copy()
    for i in regles_possibles:             #Eliminer règles donc la conclusion est incompatible avec la situation (et celles déjà appliquées)
        r  = rulebase.rules[i]
        if (r.conclusion[0] in rulebase.S) or (not rulebase.compatible([r])) or (i in deja_appliquees):               #eliminer aussi les règles dont les conclusions sont déjà dans S
            temp.remove(i)
    regles_possibles = temp

    if len(regles_possibles) > 1:
        output.append("Plusieurs règles correspondent à la situation:")
        for i in regles_possibles:
            output.append(f"- Règle {i} : {rulebase.rules[i]}")

        C_matrix = rulebase.compatibility_matrix(regles_possibles)
        rows_to_remove = set(np.where(C_matrix == 1)[0])

        for i in rows_to_remove:
            for j in range(len(regles_possibles)):
                if C_matrix[i, j] == 1:
                    r1_index = regles_possibles[i]
                    r2_index = regles_possibles[j]
                    output.append(f"La règle {r2_index} est prioritaire sur la règle {r1_index}, on écarte la règle {r1_index}. \n")

        regles_possibles = [r for i, r in enumerate(regles_possibles) if i not in rows_to_remove]

    return {
        "output":output,
        "options": [rulebase.rules[i] for i in regles_possibles],
        "indices": regles_possibles
    }


#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

#def generation_extension ():


#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#


def choix_exception(distance_method, rulebase, selection_fct_and_args,regle_choisie):
    selection_fct = selection_fct_and_args[0]
    args = selection_fct_and_args[1:]
    selected_indices = globals()[selection_fct](getattr(rulebase, distance_method)(regle_choisie), *args)
    indices_similaires,exceptions_associees = exceptions(rulebase, selected_indices)
    return {"indices":indices_similaires,
            "options":[rulebase.rules[i] for i in indices_similaires],
            "exceptions associées":[[rulebase.rules[i] for i in liste] for liste in exceptions_associees]}

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def exceptions(Rb, selected_indices):
    filtre = []
    excep = []
    for i in selected_indices:
        r1 = Rb.rules[i]
        liste_exceptions = []                # liste des exceptions de la règle i
        for j,r2 in enumerate(Rb.rules):                # On compare avec toutes les autres règles pour détecter les exceptions associées
            if j == i:
                continue
            if is_a_in_b(r1.premises, r2.premises):             # Si on a des prémices incluses dans r2 on étudie la compatibilité des ccl
                conclusions1 = r1.conclusion
                conclusions2 = r2.conclusion
                if check_conflict(conclusions1, conclusions2):               # Si elles sont incompatibles on sélectionne la règle
                    filtre.append(i)
                    liste_exceptions.append(j)
                else:
                    if not Rb.compatible([r1,r2]):              # Si elles sont incompatibales on sélectionne la règle
                        filtre.append(i)
                        liste_exceptions.append(j)
        if len(liste_exceptions)>0:
            excep.append(liste_exceptions)
    return filtre,excep

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def init_rule_base2():
    Rb = Rule_Base()
    Rb.add_W([
        "interdit <=> ~ autorisé",
        "~ ( moins_30 & entre30_50 ) & ~ ( moins_30 & plus_50 ) & ~ ( entre30_50 & plus_50 )",
    ])
    Rb.add_rules(
        [["cycliste", "traverse_parc","écouteurs"],
         ["cycliste", "traverse_parc", "écouteurs","~passants"],
         ["véhicule", "traverse_feu_rouge"],
         ["véhicule", "etat_urgence", "traverse_feu_rouge"],
         ["véhicule", "traverse_parc"],
         ["véhicule", "etat_urgence"],
         ["véhicule", "etat_urgence", "autorisé"]],
        [["interdit"], ["autorisé"],["interdit"], ["autorisé"], ["interdit"], ["gyrophare_allume"],["~amende","test"]]
    )
    return Rb

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

def init_rule_base3():
    Rb = Rule_Base()
    Rb.add_W([
        "interdit <=> ~ autorisé",
        "~ ( moins_30 & entre30_50 ) & ~ ( moins_30 & plus_50 ) & ~ ( entre30_50 & plus_50 )"
    ])
    Rb.add_rules(
        [["véhicule", "traverse_feu_rouge"],
         ["véhicule", "etat_urgence", "traverse_feu_rouge"],
         ["véhicule", "traverse_parc"],
         ["véhicule", "etat_urgence"],
         ["véhicule", "etat_urgence", "autorisé"]],
        [["interdit"], ["autorisé"], ["interdit"], ["gyrophare"],["~amende","test"]]
    )
    return Rb

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

###### PARSAGE ######

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def get_var_from_index(token_to_var, i):                # renvoie la variable qui correspond à l'indice demandé dans le dictionnaire
    for index, var in token_to_var:
        if index == i:
            return var
    return None

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def formula_creator(tokens, token_to_var):                  # va créer une formule à partir d'une liste de tokens et d'une liste de variables (avec leur position)
    stack = []              # Endroit où on va stocker la formule
    i = 0                   # indice d'avancement
    neg = False                 # négation

    while i < len(tokens):                  # On boucle sur les tokens
        token = tokens[i]                   # token actuel

        if token == ")":                    # erreur lors de la fermeture d'une parenthèse sans ouverture préalable
            raise ValueError("Invalid formula: ')' without matching '('")

        elif token == "(":                  # Si on ouvre une parenthèse on va faire un appel récursif sur la partie entre parenthèses
            sub_tokens, j = extract_subtokens(tokens, i)                    # appel de extract_subtokens pour trouver la fin de la parenthèse
            token_to_var_local = token_to_var.copy()                # copie pour ne pas modifier la version générale
            token_to_var_local[:, 0] = token_to_var_local[:, 0] - (i + 1)               # décalage des indices pour correspondre à la partie entre parenthèses
            sub_formula = formula_creator(sub_tokens, token_to_var_local)                  # appel récursif sur la partie entre parenthèses
            stack.append(~sub_formula if neg else sub_formula)                  # On rajoute dans stack la partie de formule qu'on vient de calculer, si il restait une négation identifiée plus tôt on la prends en compte
            neg = False             # ré-initialisation de neg
            i = j               # On saute à l'indice de fin de parenthèse

        elif token == "~":
            neg = not neg               # Si on détecte une négation, on inverse la valeur de neg (ça permet de traiter les cas du type ~~~ qui est équivalent à juste ~)

        elif token in ["&", "|"]:                   # Si on a un opérateur & ou | qui nécessite de connaître la formule à droite et à gauche on calcule la partie droite (on a déjà la gauche dans stack)
            if len(stack) < 1:
                raise ValueError(f"Operator {token} missing left operand")
            left = stack.pop()
            i += 1
            while i < len(tokens) and tokens[i] == "~":                 # cas des négations
                neg = not neg
                i += 1
            if i >= len(tokens):                    # formule incomplète
                raise ValueError(f"Operator {token} missing right operand")
            right, i = eval_subformula(tokens, token_to_var, i, neg)                # on évalue la sous-formule droite
            neg = False
            stack.append(left & right if token == "&" else left | right)                # On ajoute dans stack

        else:
            var = get_var_from_index(token_to_var, i)               # Initialisation de stack avec une variable si la chaîne commence comme ça
            if var is None:
                raise ValueError(f"Unknown variable: '{token}' at index {i}")
            stack.append(~var if neg else var)
            neg = False

        i += 1
    if neg:
        raise ValueError("Dangling '~' with no variable")
    if len(stack) != 1:
        raise ValueError("Invalid formula: unable to reduce to single expression")
    return stack[0]

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def extract_subtokens(tokens, start):               # On isole les parties entre parenthèses
    depth = 1
    j = start + 1
    while j < len(tokens):              # depth permet de vérifier qu'on ouvre/ferme le bon nombre de parenthèses
        if tokens[j] == "(":
            depth += 1
        elif tokens[j] == ")":
            depth -= 1
            if depth == 0:              # On sort si on a fermé la parenthèse de départ
                break
        j += 1
    if j == len(tokens):
        raise ValueError("Parenthesis not closed")
    return tokens[start + 1:j], j               # On renvoie la partie entre parenthèses et l'indice de fin de la parenthèse

#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def eval_subformula(tokens, token_to_var, i, neg):
    if tokens[i] == "(":                    # Si c'est une parenthèse on fait juste comme dans le cas général des parenthèses pour calculer tout le bloc
        sub_tokens, j = extract_subtokens(tokens, i)
        token_to_var_local = token_to_var.copy()
        token_to_var_local[:, 0] = token_to_var_local[:, 0] - (i + 1)
        sub_formula = formula_creator(sub_tokens, token_to_var_local)
        return ~sub_formula if neg else sub_formula, j
    else:                   # On ne gère pas le cas des négations vu qu'il a été traité avant l'appel de la fonction
        var = get_var_from_index(token_to_var, i)
        if var is None:
            raise ValueError(f"Variable at position {i} not found")
        return ~var if neg else var, i                  # On renvoie la sous-formule et l'indice de fin
    
#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------#

'''TEST OK'''
def str_to_formula(formula_str, Rb):                # à partir d'un string crée une formule pour W
    tokens = formula_str.split(" ")             # le séparateur du string est le caractère espace

    if sum(tokens.count(op) for op in ["<=>", ">>", "<<"]) > 1:                 # On considère des formules avec 1 seul opérateur du type <=> >> << maximum
        raise ValueError("Only one main binary operator ('<=>', '>>', '<<') allowed")

    var_tokens = []             # On va créer des sous listes avec les variables qu'on va utiliser et leur position dans la chaîne de caractères
    var_indices = []

    for i, token in enumerate(tokens):
        if token not in ["<=>", "~", ">>", "<<", "&", "|", "(", ")"]:                   # Si le token n'est pas un opérateur, on crèe une variable
            var_tokens.append(token)
            var_indices.append(i)

    var_objs = list_to_vars(Rb.Var_dictionnary, var_tokens)                 # On crée les variables correspondantes

    token_to_var = np.array(list(zip(var_indices, var_objs)), dtype=object)                 # np.array qui contient des tuples associant la variable à sa position dans la chaîne de caractères

    if "<=>" in tokens:                 # On regarde les 3 cas possibles d'opérateurs principaux, on divise à droite et à gauche de l'opérateur puis on appelle formula_creator poru créer les formules correspondantes
        idx = tokens.index("<=>")
        left = formula_creator(tokens[:idx], token_to_var)
        token_to_var[:, 0] = token_to_var[:, 0] - (idx + 1)  # Ajuste les indices pour le sous-tableau de droite
        right = formula_creator(tokens[idx+1:], token_to_var)
        return left.iff(right)

    elif ">>" in tokens:
        idx = tokens.index(">>")
        left = formula_creator(tokens[:idx], token_to_var)
        token_to_var[:, 0] = token_to_var[:, 0] - (idx + 1)
        right = formula_creator(tokens[idx+1:], token_to_var)
        return left >> right

    elif "<<" in tokens:
        idx = tokens.index("<<")
        left = formula_creator(tokens[:idx], token_to_var)
        token_to_var[:, 0] = token_to_var[:, 0] - (idx + 1)
        right = formula_creator(tokens[idx+1:], token_to_var)
        return left << right

    else:
        return formula_creator(tokens, token_to_var)