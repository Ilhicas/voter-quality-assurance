from flask import Flask, render_template
from zeep import Client

app = Flask(__name__)
client_0 = Client('http://localhost:9000/soap/insulincalculator?wsdl')
client_1 = Client('http://localhost:9000/soap/insulincalculator?wsdl')
client_2 = Client('http://localhost:9000/soap/insulincalculator?wsdl')
clients = [client_0, client_1, client_2]

class Voter():
    #TODO Class implementation
    def __init__(self):
        self.todo = 'TODO'
    
    def _call_client(self):
        pass

#Global Voter
voter = Voter()

@app.route("/", methods=["GET"])
def index():
    return render_template("index.html")

@app.route("/insulindosecalculator", methods=["GET"])
def insulin_calculator():
    #TODO Voter.method invokation and returns accordingly
    return None
