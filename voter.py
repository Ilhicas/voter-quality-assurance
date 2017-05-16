from flask import Flask, render_template
from zeep import Client
from multiprocessing.dummy import Pool
import collections
import random

app = Flask(__name__)
client_0 = Client('http://localhost:9000/soap/insulincalculator?wsdl')
client_1 = Client('http://localhost:9000/soap/insulincalculator?wsdl')
client_2 = Client('http://localhost:9000/soap/insulincalculator?wsdl')
clients = [client_0, client_1, client_2]

class Voter():
    #TODO Class implementation
    def __init__(self):
        self.todo = 'TODO'
        self.pool = Pool(3)
        self.clients = clients
        self.results = []

    def collect_results(self, result):
        self.results.append(result)

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
        clients_ids = random.sample(xrange(1,4), 3)
        for _id in clients_ids:
            self.pool.apply_async(self.clients[_id].mealtimeInsulinDose, (weight,), callback= self.collect_results)
            if len(self.results) > 1 and self.vote():
                self.pool.terminate()
                return self.vote(discard=True)
        
        self.vote(discard=True)
        return None
    
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
        
        if 3 in voter.keys():
            if discard:
                self.results = []
            return voter[3]

        if 2 in voter.keys():
            if discard:
                self.results = []
            return voter[2]
        
        if discard:
            self.results = []
        #No majority reached , return None
        return None
            

#Global Voter
voter = Voter()

@app.route("/", methods=["GET"])
def index():
    return render_template("index.html")

@app.route("/insulindosecalculator", methods=["GET"])
def insulin_calculator():
    #TODO Voter.method invokation and returns accordingly
    return None
