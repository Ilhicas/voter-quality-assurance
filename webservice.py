from flask import Flask
from flask_spyne import Spyne
from spyne.protocol.soap import Soap11
from spyne.model.primitive import Unicode, Integer
from spyne.model.complex import Iterable
#if  one unit of insulin processes 12g of mealtime carbohydrates, it will drop blood sugar by  50  mg/dl  in  an  average  individual
avg_processed_carbohydrates = 12
avg_sugar_drop = 50
ratio = 0.55

app = Flask(__name__)
spyne = Spyne(app)

class InsulinDoseCalculator(spyne.Service):

    __service_url_path__ = '/soap/insulincalculator'
    __in_protocol__ = Soap11(validator='lxml')
    __out_protocol__ = Soap11()

    """Calculates the number of insulin units needed after one meal.
    Keyword arguments:
    carbo_meal -- total grams of carbohydrates in the meal (between 60g and 120g)
    carbo_proc -- total grams of carbohydrates processed by 1 unit of rapid acting insulin (between 10g/unit and 15g/unit, but the typical value is 12g/unit)
    act_blood_sugar -- actual blood sugar level measured before the meal (between 120mg/dl and 250mg/dl)
    tgt_blood_sugar -- target blood sugar before the meal (between 80mg/dl and 120mg/dl)
    sensitivity -- individual sensitivity (between 15mg/dl and 100mg/dl per unit of insulin)
    Returns: the number of units of rapid acting insulin needed after a meal (i.e., bolus insulin replacement dose)
    """
    @spyne.srpc(Integer, Integer, Integer, Integer, Integer, _returns=Integer)
    def mealtimeInsulinDose(carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensitivity):
        if carbo_meal > 120 or carbo_meal < 60:
            return -1

        if carbo_proc > 15 or carbo_proc < 10:
            return -1

        if act_blood_sugar > 250 or act_blood_sugar < 120:
            return -1

        if tgt_blood_sugar > 120 or tgt_blood_sugar < 80:
            return -1

        if sensitivity > 100 or sensitivity < 15:
            return -1

        """In the special case when the target blood sugar level is greater
        than the actual blood sugar level, the return value of this method
        is zero (no insulin).
        """
        if tgt_blood_sugar > act_blood_sugar:
            return 0

        """The high  blood  sugar  dose  is  calculated  by  taking  the  blood
        sugar  level  measured  before the meal minus the target blood sugar
        before the meal, and dividing that amount  by  the  amount  that  one
        unit  of  the  used  insulin  will  decrease  in  that  particular
        individual (i.e., individual sensitivity).
        """
        high_blood_sugar_dose = (float(act_blood_sugar) - float(tgt_blood_sugar))/float(sensitivity)

        """The carbohydrate dose equals the total grams of carbohydrates
        consumed during the meal divided by the number of grams
        processed by one unit of the used rapid acting insulin.
        """

        # carbo_proc = carbo_proc / sensitivity

        carbohydrate_dose = float(carbo_meal)/float(carbo_proc)

        """
        This value is adjusted according to individual sensitivity, by
        stipulating that if one unit of insulin processes 12g of mealtime
        carbohydrates, it will drop blood sugar by 50 mg/dl in an average
        individual (proportions are maintained if the insulin used
        processes a higher or lower value of carbohydrates, compared
        to the reference of 12g/unit).
        """


        """The number of units of rapid acting insulin after a meal
        is equal to the high blood sugar dose plus the carbohydrate dose.
        """
        mealtimeDose = high_blood_sugar_dose + carbohydrate_dose
        print(mealtimeDose)
        return int(mealtimeDose)

    """Calculates the total number of units of insulin needed between meals
    Keyword arguments:
    weight -- Weight in kilograms (between 40kg and 130kg)
    Returns: Background insulin dose
    """
    @spyne.srpc(Integer, _returns=Integer)
    def backgroundInsulinDose(weight):
        if weight > 130 or weight < 40:
            return -1

        """
        The general approach is to take 0.55 multiplied by the weight in
        kilograms as the total (i.e., mealtime plus background) daily insulin
        requirement. The background insulin dose is generally 50%  of that total.
        """
        
        return int((ratio * weight)/2)

    """Determines an individual's sensitivity to one unit of insulin
    Keyword arguments:
    activity_level -- today's physical activity level (between 0 and 10)
    k_activity -- K samples of physical activity level in some day (between 0 and 10)
    k_drops -- K  samples  of  drops  in  blood  sugar  from  one  unit  of  insulin  in  that  day  (between  15mg/dl and 100mg/dl)
    Returns: Background insulin dose
    """
    @spyne.srpc(Integer, Integer(max_occurs="unbounded") , Integer(max_occurs="unbounded"), _returns=Integer)
    def personalSensitivityToInsulin(activity_level, k_activity, k_drops):
        _k_activity = [float(element) for element in k_activity]
        _k_drops = [float(element) for element in k_drops]
        print "_k_activiity", _k_activity
        print "_k_drops", _k_drops
        print "activity",activity_level

        if activity_level > 10 or activity_level < 0:
            return -1

        if len(_k_activity) > 10 or len(_k_activity) < 2:
            return -1

        for drop in _k_drops:
            if drop > 100 or drop < 15:
                return -1

        for activity in _k_activity:
            if drop > 10 or drop < 0:
                return -1

        if len(_k_activity) != len(_k_drops):
            return -1

        mean_k_drops = sum(_k_drops)/float(len(_k_drops))
        mean_k_activity = sum(_k_activity)/float(len(_k_activity))

        beta_up = beta_down = 0
        for i in range(len(_k_activity)):
            beta_up += (_k_activity[i] - mean_k_activity) * (_k_drops[i] - mean_k_drops)
            beta_down += pow(_k_activity[i] - mean_k_activity,2)

        beta = beta_up/beta_down

        alpha = mean_k_drops - (beta * mean_k_activity)
        
        return int(alpha + (beta * activity_level))

if __name__ == '__main__':
    app.run(host = '0.0.0.0',port=9000)

