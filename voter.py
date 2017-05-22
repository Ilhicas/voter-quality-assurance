from flask import Flask, render_template, request, jsonify
from zeep import Client
from multiprocessing.dummy import Pool
import collections
import random
import time

app = Flask(__name__)

error_message = "It  was  not  possible  to  calculate the insulin dose; please try again."

class ClientProxy():
    def __init__(self, url):
        self.url = url
        self.proxy = Client(url)

    def backgroundInsulinDose(self, weight):
        started = time.time()
        return [int(self.proxy.service.backgroundInsulinDose(weight)), self.url, (time.time() - started)]

    def mealtimeInsulinDose(self, carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensivity):
        started = time.time()
        return [int(self.proxy.service.mealtimeInsulinDose(carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensivity)), self.url, (time.time() - started)]

    def personalSensitivityToInsulin(self, activity_level, k_activity, k_drops):
        started = time.time()
        return [int(self.proxy.service.personalSensitivityToInsulin(activity_level, k_activity, k_drops)), self.url, (time.time() - started)]

class ClientList():

    def __init__(self):
        self.clients = []
        self.setup()

    def get_clients(self):
        return self.clients

    def setup(self):
        try:
            client = ClientProxy("http://10.17.1.23:8081/insulin?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.8:8080/InsulinDoseCalculator/ws/insulin-dose-calculator?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.21:8081/insulincalculator?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.17:8081/insulindosecalculator?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.13:8080/InsulinDoseCalculator_WebService_QCS/services/InsulinDoseCalculator?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.16:8080/deploy/services/insulin?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.25:9000/soap/insulincalculator?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.10:8080/WebServiceQCS/services/InsulinDoseCalculator?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.26:9999/InsulinCalculator?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.6:8080/InsulinDoseCalculator/insulin?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.24:8081/InsulinDoseCalculatorEndpoint?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.14:9000/InsulinDoseCalculator?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://10.17.1.19:8080/insulin/insulin?wsdl")
            self.clients.append(client)
        except:
            pass
        try:
            client = ClientProxy("http://ec2-54-218-110-193.us-west-2.compute.amazonaws.com:8081/mf_calculator?wsdl")
            self.clients.append(client)
        except:
            pass

class Voter():

    def __init__(self, client_list):
        self.pool = Pool(3)
        self.clients = client_list
        self.results = list()
        self.time_to_live = 4.00
        self.show_results = dict()

    def collect_results(self, result):

        self.results.append(result[0])
        self.show_results[result[1]] = [result[0], result[2]]


    def _mealtimeInsulinDose(self, carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensivity, started = None):

        clients_ids = random.sample(xrange(0,len(self.clients)), 3)
        if started is None:
            started = time.time()

        for _id in clients_ids:
            self.pool.apply_async(self.clients[_id].mealtimeInsulinDose, (carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensivity,), callback= self.collect_results)
            if len(self.results) > 1 and self.vote():
                self.pool.terminate()
                return self.vote(), self.show_results

        while((time.time() - started < self.time_to_live) and not self.vote()):
            if len(self.results) == 3:
                self.results = []
                self._mealtimeInsulinDose(carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensivity, started=started)

        self.pool.terminate()
        return self.vote(), self.show_results


    def _backgroundInsulinDose(self, weight, started = None):
        clients_ids = random.sample(xrange(0,len(self.clients)), 3)
        if started is None:
            started = time.time()

        for _id in clients_ids:
            self.pool.apply_async(self.clients[_id].backgroundInsulinDose, (weight,), callback= self.collect_results)
            if len(self.results) > 1 and self.vote():
                self.pool.terminate()
                return self.vote(), self.show_results

        while((time.time() - started < self.time_to_live) and not self.vote()):
            if len(self.results) == 3:
                self.results = []
                self._backgroundInsulinDose(weight, started=started)


        self.pool.terminate()
        return self.vote(), self.show_results

    def _personalSensitivityToInsulin(self, activity_level, k_activity, k_drops, started=None):
        clients_ids = random.sample(xrange(0,len(self.clients)), 3)
        if started is None:
            started = time.time()

        for _id in clients_ids:
            self.pool.apply_async(self.clients[_id].personalSensitivityToInsulin, (activity_level, k_activity, k_drops,), callback= self.collect_results)
            if len(self.results) > 1 and self.vote():
                self.pool.terminate()
                return self.vote(), self.show_results

        while((time.time() - started < self.time_to_live) and not self.vote()):
            if len(self.results) == 3:
                self.results = []
                self._personalSensitivityToInsulin(activity_level, k_activity, k_drops, started=started)

        self.pool.terminate()
        return self.vote(), self.show_results

    def vote(self):
        voter = collections.Counter(self.results)
        try:
            voter = dict(voter)
            for result, votes in voter.iteritems():
                if votes >= 2:
                    return result

            #No majority reached , return None
        except Exception as e:
            #Object counter is not yet built
            pass

        return None


#Global Clients List
client_list = ClientList().get_clients()

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

    response, details = Voter(client_list)._mealtimeInsulinDose(carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensitivity)

    if response == -1 or response is None:
        response = error_message

    return render_template("response.html", response=response, details=details )


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
    response, details = Voter(client_list)._backgroundInsulinDose(weight)
    if response == -1 or response is None:
        response = error_message

    return render_template("response.html", response=response, details=details )


"""Determines an individual's sensitivity to one unit of insulin
Keyword arguments:
activity_level -- today's physical activity level (between 0 and 10)
k_activity -- K samples of physical activity level in some day (between 0 and 10)
k_drops -- K  samples  of  drops  in  blood  sugar  from  one  unit  of  insulin  in  that  day  (between  15mg/dl and 100mg/dl)
Returns: Background insulin dose
"""
@app.route("/personalSensitivityToInsulin", methods=["GET"])
def personalSensitivityToInsulin():
    carbo_meal = request.args.get('carbo_meal')
    carbo_proc = request.args.get('carbo_proc')
    act_blood_sugar = request.args.get('act_blood_sugar')
    tgt_blood_sugar = request.args.get('tgt_blood_sugar')
    activity_level = request.args.get('activity_level')
    k_activity = request.args.getlist('k_activity')
    k_drops = request.args.getlist('k_drops')
    if not activity_level or not k_activity or not k_drops:
        return render_template("index.html", response="Failed to calculate")
    k_activity_final = list()
    k_drops_final = list()
    for k in k_activity:
        if k:
            k_activity_final.append(int(k))
    for k in k_drops:
        if k:
            k_drops_final.append(int(k))

    print k_activity_final
    print k_drops_final
    # Call webservices and do voting stuff for personalSensitivityToInsulin here
    # ....
    activity_level = int(activity_level)

    response, first_details = Voter(client_list)._personalSensitivityToInsulin(activity_level, k_activity_final, k_drops_final)
    response, second_details = Voter(client_list)._mealtimeInsulinDose(carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, response)

    if response == -1 or response is None:
        response = error_message

    return render_template("response.html", response=response, details=first_details, second_details = second_details)

if __name__ == '__main__':
    app.run(debug=True, threaded=True)
