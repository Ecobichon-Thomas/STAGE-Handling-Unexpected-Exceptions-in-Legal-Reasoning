from flask import Flask, request, render_template, session, redirect
from mistralai import Mistral
from logic import *
from lib_logic2 import *

app = Flask(__name__)
app.secret_key = "test75591729"

API_KEY = "485M73hYCA2ohQ7YykmzYLMo1zMKUjY7"
MODEL = "mistral-medium"
client = Mistral(api_key=API_KEY)

#----------------------------------------------------------------------------------------------#

DISTANCE_METHODS = {"Distance de Hamming": "dist_hamming"}

SELECTION_METHODS = {"Seuil": "select_fct_treshold",
                     "Minimale":"select_fct_minimal",
                     "Seuil Minimal":"select_fct_treshold_minimal"}

@app.route("/")
def index():
    return render_template(
        "Application.html",
        distances=list(DISTANCE_METHODS.keys()),
        selection=list(SELECTION_METHODS.keys()),
        dist_map=DISTANCE_METHODS,
        sel_map=SELECTION_METHODS)

@app.route("/start")
def start():
    session["user_id"] = 42
    session["score"] = 0
    return "Session démarrée."

@app.route("/reset")
def reset():
    session.clear()
    return redirect("/")

@app.route("/traiter", methods=["POST"])
def traiter():
    scenario = request.form.get('scenario', "").strip()             # Scenario dans le système, déjà décomposé
    print("scenario",scenario)
    resultat = request.form.get("resultat", "")             # Décomposition de ce scénario
    scenario1 = request.form.get("scenario1", "").strip()           # Nouveau scénario si l'utilisateur en a fourni un
    complement = request.form.get("complement", None)         #Complément au prompt si l'utilisateur n'est pas satisfait par la décomposition

    if scenario1 != "":               # Si l'utilisateur soumet un nouveau scénario on ré-initialise la mémoire, sinon on la conserve
        print("reset")
        session.clear()
        scenario = scenario1
    if scenario == "":              # Cas scénario vide
        return render_template("Application.html", resultat="Aucun scénario fourni.")
        
    choice = request.form.get("user_choice", None)              # On récupère le choix de l'utilisateur si il y en a un (choix de quelle règle appliquer)
    Rb = init_rule_base2()              # Initialisation de la base de règles

    if not session.get("decomposition") or (complement != None):                # Si on a la decomposition de S en mémoire ou que la décomposition n'est pas satisfaisante
        premises = ';'.join(Rb.Var_dictionnary._variables.keys())
        print(premises)
        prompt = ("Tu es un expert des textes juridiques et de la décomposition de situations juridiques en prémices"
        +"Décompose le scénario sous la forme d'une liste de prémices, en utilisant le caractère ; comme séparateur dans ton retour."
        +"Voici un exemple de scénario, 'Une voiture a traversé un feu rouge', le résultat attendu serait, 'véhicule;traverse_feu_rouge': \n " 
        +"Scénario: \n"+ scenario 
        +"\n Liste des prémices déjà en mémoire qui peuvent être réutilisés si le scénario comporte des éléments similaires:"
        +premises
        +"\n Ne crée de nouveau prémice que si c'est nécessaire."
        +"\n Ne rajoute des prémices que lorsque tu as de l'information explicite, ne fait pas d'inférence. "
        +"\n Par exemple une ambulance n'est pas forcément en état d'urgence et n'a PAS FORCEMENT son gyrophare allumé! C'est le cas uniquement si c'est PRECISE, généralise cet exemple à tout les prémices"
        +"\n Ton retour ne doit comporter que la liste des prémices correspondant au scénario dans le format demandé"
        +"\n Si certains prémices sont des négations, utilise la caractère ~ au début de la chaîne. Par exemple:"
        +"\n 'Une ambulance avec son gyrophare n'a pas traversé le parc' donnerait:"
        +"\n véhicule;gyrophare;etat_urgence;~traverse_parc" 
        +"\n 'et, Une ambulance ne s'est pas arrêté au feu rouge' donnerait:"
        +"\n véhicule;traverse_feu_rouge" 
        +"\n Ton retour sera utilisé dans le contexte de textes juridiques. Adapte tes réponses à ce contexte."
        +"\n Attention, veille à créer des catégories qui font sens, un vélo peut être vu comme un véhicule "
        +"mais pas dans le contexte de la règle qui interdit aux véhicules motorisés de traverser un parc "
        +"\n Attention!! ne renvoie que un string de la forme demandée, pas d'explications!!!")

        if (complement != None):
            S_join = ';'.join(session.get("decomposition"))
            prompt += ("Voici la décomposition que tu as proposé à l'étape précédente:"+S_join
            +"Voici des précisions de l'utilisateur pour l'améliorer:"+complement+"recommence en les prenant en compte")
        
        chat_response = client.chat.complete( model=MODEL , messages=[ {"role": "user","content": (prompt)} ] )
        resultat = chat_response.choices[0].message.content
    
        S = resultat.split(";")

        session["decomposition"] = S
        session["appliquees"] = []
        log = "Génération d'une extension:"
    else :
        resultat = request.form.get("resultat", "")
        S = session.get("decomposition", [])
        log = request.form.get("log", "")

    deja_appliquees = session.get("appliquees", [])

    if (choice is not None) and (choice != "-1"):                 # Si l'utilisateur a choisi
        # on ajoute directement la règle puis on passe à la suite
        deja_appliquees = session.get("appliquees", [])

        choice = int(choice)
        ccl = Rb.rules[choice].conclusion              # robuste pour passage aux listes de conclusions
        for c in ccl:                   # On traduit en string les négations pour pouvoir les entrer dans S
            if isinstance(c,Not):
                temp = "~"+c.children[0].name
            else:
                temp = c.name
            if temp not in S:
                S.append(temp)

        log += "\n \n"+f"On applique la règle {choice} : {Rb.rules_original[choice]} "

        deja_appliquees.append(choice)
        session["appliquees"] = deja_appliquees

    analyse = scenario_check_web4_test(S, Rb,deja_appliquees)                # Règles applicables
    indices = analyse.get("indices",[])              # Indices des règles en question
    options = analyse.get("options",[])
    output = analyse.get("output","")

    if len(indices)==0 or choice=="-1":              # Plus aucune règle applicable, on s'arrête de générer l'extension
        if len(deja_appliquees) == 0:               # Si on a appliqué aucune règle on renvoie une erreur
            return render_template("Application.html",
                                   resultat=resultat,
                                   scenario=scenario,
                                   No_rule = True)
        
        else:               # Sinon on passe à la génération des exceptions
            log +="\n \n Il n'y a plus de règles applicables: Fin de la génération de l'extension"
            return render_template("Application.html",
                                scenario=scenario,
                                resultat=resultat,
                                extension = True,
                                log=log,
                                distances=list(DISTANCE_METHODS.keys()),
                                selection=list(SELECTION_METHODS.keys()),
                                dist_map=DISTANCE_METHODS,
                                sel_map=SELECTION_METHODS)
        
    else:               # Si plusieurs règles possibles, on transmet les choix
        log +="\n".join(output)
        return render_template("Application.html",
                                conflit=True,
                                resultat=resultat,
                                options=options,
                                indices=indices,
                                scenario=scenario,
                                log=log)

@app.route("/exceptions", methods=["POST"])
def exception():
    dist_choice_label = request.form.get("distances", list(DISTANCE_METHODS.keys())[0]).strip()
    sel_choice_label = request.form.get("selection", list(SELECTION_METHODS.keys())[0])
    distance_method = DISTANCE_METHODS[dist_choice_label]
    selection_method = SELECTION_METHODS[sel_choice_label]

    scenario = request.form.get('scenario', "").strip()
    log = request.form.get("log", "")
    seuil = request.form.get("seuil")

    deja_appliquees = session["appliquees"]

    if seuil is not None:
        arguments = list([selection_method,seuil])
    else:
        arguments = list([selection_method])

    resultat = request.form.get("resultat", "")
    S = resultat.split(";")
    Rb = init_rule_base2()
    Rb.init_S(S)

    choix_ex = choix_exception(distance_method, Rb, arguments,deja_appliquees[-1])
    print("choix_ex",choix_ex)

    if choix_ex["options"] == []:
        return render_template(
        "Application.html",
        resultat=resultat,
        scenario = scenario,
        no_exception = True,
        distances=list(DISTANCE_METHODS.keys()),
        selection=list(SELECTION_METHODS.keys()),
        dist_map=DISTANCE_METHODS,
        sel_map=SELECTION_METHODS,
        log=log)

    return render_template(
        "Application.html",
        resultat=resultat,
        scenario = scenario,
        options_rules = choix_ex["options"],
        indices_rules = choix_ex["indices"],
        options_exceptions = choix_ex["exceptions associées"],
        distances=list(DISTANCE_METHODS.keys()),
        selection=list(SELECTION_METHODS.keys()),
        dist_map=DISTANCE_METHODS,
        sel_map=SELECTION_METHODS,
        log=log)

@app.route("/proposition", methods=["POST"])
def proposition():

    scenario = request.form.get('scenario', "").strip()
    log = request.form.get("log", "")

    regle_exception = request.form.get("choix_regle_exception", "")

    resultat = request.form.get("resultat", "")
    S = resultat.split(";")
    Rb = init_rule_base2()
    Rb.init_S(S)

    return render_template(
        "Application.html",
        regle_exception = regle_exception,
        resultat=resultat,
        scenario = scenario,
        log=log)

if __name__ == "__main__":
    app.run(debug=True)

#----------------------------------------------------------------------------------------------#
