from flask import Flask, render_template, request, jsonify
from zeep import Client
from multiprocessing.dummy import Pool
import collections
import random
import time

app = Flask(__name__)
client_0 = Client('http://10.17.1.23:8081/insulin?wsdl')
client_1 = Client('http://10.17.1.3:8080/services/InsulinDoseCalculator?wsdl')
client_2 = Client('http://10.17.1.8:8080/InsulinDoseCalculator/ws/insulin-dose-calculator?wsdl')
clients = [client_0, client_1, client_2]

class Voter():
    #TODO Class implementation
    def __init__(self):
        self.todo = 'TODO'
        self.pool = Pool(3)
        self.clients = clients
        self.results = []
        self.time_to_live = 4.00
    def collect_results(self, result):
        self.results.append(int(result))
        print self.results

    def _mealtimeInsulinDose(self, carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensivity):
        clients_ids = random.sample(xrange(1,4), 3)
        for _id in clients_ids:
            self.pool.apply_async(self.clients[_id].mealtimeInsulinDose, (carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensivity,), callback= self.collect_results)
            if len(self.results) > 1 and self.vote():
                self.pool.terminate()
                return self.vote(discard=True)
        
        self.vote(discard=True)
        return None
    
    def _backgroundInsulinDose(self, weight):
        started = time.time()
        clients_ids = random.sample(xrange(0,3), 3)
        for _id in clients_ids:
            self.pool.apply_async(self.clients[_id].service.backgroundInsulinDose, (weight,), callback= self.collect_results)
            if len(self.results) > 1 and self.vote():
                self.pool.terminate()
                return self.vote(discard=True)
        
        while((time.time() - started < self.time_to_live) and not self.vote()):
            pass
        
        self.pool.terminate()
        return self.vote(discard=True)
    
    def _personalSensitivityToInsulin(self, activity_level, k_activity, k_drops):
        clients_ids = random.sample(xrange(1,4), 3)
        for _id in clients_ids:
            self.pool.apply_async(self.clients[_id].mealtimeInsulinDose, (activity_level, k_activity, k_drops,), callback= self.collect_results)
            if len(self.results) > 1 and self.vote():
                self.pool.terminate()
                return self.vote(discard=True)
        
        self.vote(discard=True)

        return None

    def vote(self, discard=False):
        voter = collections.Counter(self.results)
        
        try:
            voter = dict(voter)
            for result, votes in voter.iteritems():
                if votes == 3 or votes == 2:
                    return result
        
            #No majority reached , return None
        except Exception as e:
            #Object counter is not yet built
            print e
        return None
            

#Global Voter
voter = Voter()

@app.route("/", methods=["GET"])
def index():
    return render_template("index.html")


"""Calculates the number of insulin units needed after one meal.
Keyword arguments:
carbo_meal -- total grams of carbohydrates in the meal (between 60g and 120g)
carbo_proc -- total grams of carbohydrates processed by 1 unit of rapid acting insulin (between 10g/unit and 15g/unit, but the typical value is 12g/unit)
act_blood_sugar -- actual blood sugar level measured before the meal (between 120mg/dl and 250mg/dl)
tgt_blood_sugar -- target blood sugar before the meal (between 80mg/dl and 120mg/dl)
sensivity -- individual sensitivity (between 15mg/dl and 100mg/dl per unit of insulin)
Returns: the number of units of rapid acting insulin needed after a meal (i.e., bolus insulin replacement dose)
"""
@app.route("/mealtimeInsulinDose", methods=["GET"])
def mealtimeInsulinDose():
    carbo_meal = request.args.get('carbo_meal')
    carbo_proc = request.args.get('carbo_proc')
    act_blood_sugar = request.args.get('act_blood_sugar')
    tgt_blood_sugar = request.args.get('tgt_blood_sugar')
    sensitivity = request.args.get('sensitivity')

    if not carbo_meal or not carbo_proc or not act_blood_sugar or not act_blood_sugar or not tgt_blood_sugar or not sensitivity:
        #TODO Error message or something
        return render_template("index.html", response="Failed to calculate")

    # Call webservices and do voting stuff for mealtimeInsulinDose here
    # ....
    response = 100

    return response


"""Calculates the total number of units of insulin needed between meals
Keyword arguments:
weight -- Weight in kilograms (between 40kg and 130kg)
Returns: Background insulin dose
"""
@app.route("/backgroundInsulinDose", methods=["GET"])
def backgroundInsulinDose():
    weight = request.args.get('weight')
    if not weight:
        #TODO Error message or something
        return render_template("index.html", response="Failed to calculate")

    # Call webservices and do voting stuff for backgroundInsulinDose here
    # ....
    response = Voter()._backgroundInsulinDose(weight)
    
    response = str(response)
    return response


"""Determines an individual's sensitivity to one unit of insulin
Keyword arguments:
activity_level -- today's physical activity level (between 0 and 10)
k_activity -- K samples of physical activity level in some day (between 0 and 10)
k_drops -- K  samples  of  drops  in  blood  sugar  from  one  unit  of  insulin  in  that  day  (between  15mg/dl and 100mg/dl)
Returns: Background insulin dose
"""
@app.route("/personalSensitivityToInsulin", methods=["GET"])
def personalSensitivityToInsulin():
    activity_level = request.args.get('activity_level')
    k_activity = request.args.getlist('k_activity')
    k_drops = request.args.getlist('k_drops')
    if not activity_level or not k_activity or not k_drops:
        return render_template("index.html", response="Failed to calculate")


    # Call webservices and do voting stuff for personalSensitivityToInsulin here
    # ....
    response = 100
    return response


if __name__ == '__main__':
    app.run(debug=True)
