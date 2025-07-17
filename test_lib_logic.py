import unittest
from lib_logic2 import *

class TestFcts(unittest.TestCase):

    def setUp(self):
        self.Var_dict = VariableUnicity()

    def test_get(self):
        var1 = self.Var_dict.get("var")
        var2 = self.Var_dict.get("var")
        self.assertIsInstance(var1, Variable)
        self.assertIs(var1,var2)
    
    def test_get_many(self):
        vars = self.Var_dict.get_many(*["var","var","a","b"])
        for v in vars:
            self.assertIsInstance(v, Variable)
        self.assertIs(vars[0],vars[1])

    def test_list_to_vars(self):
        vars = list_to_vars(self.Var_dict,["interdit","~authorisé"])
        self.assertIsInstance(vars[1],Not)
        self.assertIsInstance(vars[1].children[0],Variable)
        self.assertIsInstance(vars[0],Variable)
    
    def test_Negation_Elimination(self):
        variables = list_to_vars(self.Var_dict,["~a","~d"])
        W_vars = list_to_vars(self.Var_dict,["a","~b","~c","d"])
        comparaison = list_to_vars(self.Var_dict,["b","c"])

        f1 = W_vars[0].iff(W_vars[1])
        f2= W_vars[2].iff(W_vars[3])

        W = [f1,f2]
        temp = Negation_Elimination(variables,W)
        self.assertIs(temp[0],comparaison[0])
        self.assertIs(temp[1],comparaison[1])
    
    def test_all_premises(self):
        variables = list_to_vars(self.Var_dict,["b","~c"])
        W_vars = list_to_vars(self.Var_dict,["a","~b","~c","d"])
        comparaison = list_to_vars(self.Var_dict,["b","~c","~a","d"])

        f1 = W_vars[0].iff(W_vars[1])
        f2= W_vars[2].iff(W_vars[3])

        W = [f1,f2]
        temp = all_premises(variables,W)
        self.assertIs(temp[0],comparaison[0])
        self.assertIsInstance(temp[1],Not)
        self.assertIs(temp[1].children[0],comparaison[1].children[0])
        self.assertIsInstance(temp[2],Not)
        self.assertIs(temp[2].children[0],comparaison[2].children[0])
        self.assertIs(temp[3],comparaison[3])

    def test_is_subset_equivalent(self):
        v1 = list_to_vars(self.Var_dict,["~a","~d"])
        v2 = list_to_vars(self.Var_dict,["~a","~d","c"])
        self.assertEqual(True,is_subset_equivalent(v1, v2))

    def test_get_var_from_index(self):
        var_objs = list_to_vars(self.Var_dict, ["a","b","c"])
        token_to_var = np.array(list(zip([1,3,7], var_objs)), dtype=object)
        self.assertIs(get_var_from_index(token_to_var, 3),self.Var_dict.get("b"))

    def test_extract_subtokens(self):
        token,index = extract_subtokens(["a","(","b","(","(","c",")",")",")"], 1)
        self.assertEqual(index,8)
        self.assertEqual(token,['b', '(', '(', 'c', ')', ')'])

    def test_eval_subformula(self):
        var_objs = list_to_vars(self.Var_dict, ["a","b","c"])
        token_to_var = np.array(list(zip([0,2,5], var_objs)), dtype=object)
        formula,indice  = eval_subformula(["a","(","b","&","(","c",")",")"], token_to_var, 1, True)

        vars_comp = list_to_vars(self.Var_dict,["a","b","c"])
        comparaison = ~(vars_comp[1]&(vars_comp[2]))

        self.assertEqual(formula,comparaison)
        self.assertEqual(indice,7)
    
    def test_formula_creator(self):
        tokens = ["~","a","&","(","~","~","~","b","|","c",")"]
        var_objs = list_to_vars(self.Var_dict, ["a","b","c"])
        token_to_var = np.array(list(zip([1,7,9], var_objs)), dtype=object)
        formula = formula_creator(tokens, token_to_var)

        vars_comp = list_to_vars(self.Var_dict,["a","b","c"])
        comparaison = ~vars_comp[0]&(~vars_comp[1]|(vars_comp[2]))

        self.assertEqual(formula,comparaison)

    def test_str_to_formula(self):
        Rb = Rule_Base()
        formula = str_to_formula("~ ( a & ~ ~ b ) <=> ~ ~ ~ ( a | ( ~ c & d ) | e )", Rb)

        vars_comp = list_to_vars(self.Var_dict,["a","b","c","d","e"])
        comparaison = (~(vars_comp[0]&vars_comp[1])).iff( ~(vars_comp[0]|(~vars_comp[2]&vars_comp[3])|vars_comp[4] ))

        self.assertEqual(formula,comparaison)

class TestRuleBase(unittest.TestCase):

    def setUp(self):
        self.Rb = Rule_Base()

    def test_add_rules_W_and_inclusion(self):
        self.Rb.add_W(["a <=> ~ b",
                       "~ c <=> d",
                       "~ ( e & f ) & ~ ( e & ~ g ) & ~ ( ~ g & f )",
                       "~ h >> i",
                       "j << ~ k"])
        self.Rb.add_rules([["b","~c"],
                           ["~a","d","f"], 
                           ["~j","g","d","f","b"], 
                           ["a","d","f"],
                           ["d","f"]],
                          [["h"] , ["i"] , ["h"] , ["e"] , ["~g"]])
        self.Rb.init_S(["b", "~c", "f","k"])
        included = self.Rb.inclusion([])                # On teste quelles règles peuvent s'appliquer à la situation S, on attend [0,1,3] comme résultat
        self.assertEqual([0,1,4], included)

    def test_isidentical(self):
        self.Rb.add_W(["a <=> ~ b",
                       "~ c <=> d",
                       "~ ( e & f ) & ~ ( e & ~ g ) & ~ ( ~ g & f )",
                       "~ h >> i",
                       "j << ~ k"])
        self.Rb.add_rules([["b","~c"],
                           ["~a","d","f"], 
                           ["~j","g","d","f","b"], 
                           ["a","d","f"],
                           ["d","f"]],
                          [["h"] , ["i"] , ["h"] , ["e"] , ["~g"]])
        self.Rb.init_S(["b", "d"])
        identical = self.Rb.is_identical()
        self.assertEqual(0,identical)


    def test_compatibility_matrix(self):
        self.Rb.add_W(["a <=> ~ b",
                       "~ c <=> d",
                       "~ ( e & f ) & ~ ( e & ~ g ) & ~ ( ~ g & f )",
                       "~ h >> i",
                       "j << ~ k"])
        self.Rb.add_rules([["b","~c"],
                           ["~a","d","f"], 
                           ["~j","g","d","f","b"], 
                           ["a","d","f"],
                           ["d","f"]],
                          [["h"] , ["i"] , ["h"] , ["e"] , ["~g"]])
        self.Rb.init_S(["b", "~c", "f","k"])
        mat = self.Rb.compatibility_matrix([0,1,2,3,4])
        expected = [[0,1,0,0,0],
            [0,0,1,0,0],
            [0,0,0,0,0],
            [0,0,0,0,0],
            [0,1,1,1,0]]                # règle 4 incompatible avec 2,3,4 car sa ccl incompatible avec f qui est un des pré-requis des autres

        for row1, row2 in zip(mat, expected):
            self.assertEqual(row1.tolist(), row2)     

    def test_dist_hamming(self):
        self.Rb.add_W(["a <=> ~ b",
                       "~ c <=> d",
                       "~ ( e & f ) & ~ ( e & ~ g ) & ~ ( ~ g & f )",
                       "~ h >> i",
                       "j << ~ k"])
        self.Rb.add_rules([["b","~c"],
                           ["~a","d","f"], 
                           ["~j","g","d","f","b"], 
                           ["a","d","f"],
                           ["d","f"]],
                          [["h"] , ["i"] , ["h"] , ["e"] , ["~g"]])
        dists = self.Rb.dist_hamming(0)
        self.assertEqual(dists.tolist(), [0,12,3,12,12])  # identiques

'''    @patch('builtins.input', lambda *args: '0')
    def test_scenario_check(self):
        self.Rb.add_rules([["b", "~c"]], [["a"]])
        self.Rb.init_S(["b", "~c"])
        result = Scenario_check(["b", "~c"], "dist_hamming", self.Rb, [select_fct_treshold, 2])
        self.assertEqual(result, 0)'''

if __name__ == '__main__':
    unittest.main()