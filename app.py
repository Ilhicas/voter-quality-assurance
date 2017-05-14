#if  one unit of insulin processes 12g of mealtime carbohydrates, it will drop blood sugar by  50  mg/dl  in  an  average  individual
avg_processed_carbohydrates = 12
avg_sugar_drop = 50
ratio = 0.55

class InsulinDoseCalculator:

    """Calculates the number of insulin units needed after one meal.
  Keyword arguments:
  carbo_meal -- total grams of carbohydrates in the meal (between 60g and 120g)
  carbo_proc -- total grams of carbohydrates processed by 1 unit of rapid acting insulin (between 10g/unit and 15g/unit, but the typical value is 12g/unit)
  act_blood_sugar -- actual blood sugar level measured before the meal (between 120mg/dl and 250mg/dl)
  tgt_blood_sugar -- target blood sugar before the meal (between 80mg/dl and 120mg/dl)
  sensivity -- individual sensitivity (between 15mg/dl and 100mg/dl per unit of insulin)
  Returns: the number of units of rapid acting insulin needed after a meal (i.e., bolus insulin replacement dose)
  """
    def mealtimeInsulinDose(self, carbo_meal, carbo_proc, act_blood_sugar, tgt_blood_sugar, sensivity):
        if carbo_meal > 120 or carbo_meal < 60:
            return -1

        if carbo_proc > 15 or carbo_proc < 10:
            return -1

        if act_blood_sugar > 250 or act_blood_sugar < 120:
            return -1

        if tgt_blood_sugar > 120 or tgt_blood_sugar < 80:
            return -1

        if sensivity > 100 or sensivity < 15:
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
        high_blood_sugar_dose = (act_blood_sugar - tgt_blood_sugar)/sensivity

        """The carbohydrate dose equals the total grams of carbohydrates
        consumed during the meal divided by the number of grams
        processed by one unit of the used rapid acting insulin.
        """
        carbohydrate_dose = carbo_meal/carbo_proc

        """
        This value is adjusted according to individual sensitivity, by
        stipulating that if one unit of insulin processes 12g of mealtime
        carbohydrates, it will drop blood sugar by 50 mg/dl in an average
        individual (proportions are maintained if the insulin used
        processes a higher or lower value of carbohydrates, compared
        to the reference of 12g/unit).
        """
        carbohydrate_dose = (carbohydrate_dose * avg_sugar_drop)/avg_processed_carbohydrates

        """The number of units of rapid acting insulin after a meal
        is equal to the high blood sugar dose plus the carbohydrate dose.
        """
        mealtimeDose = high_blood_sugar_dose + carbohydrate_dose

        return mealtimeDose

    """Calculates the total number of units of insulin needed between meals
    Keyword arguments:
    weight -- Weight in kilograms (between 40kg and 130kg)
    Returns: Background insulin dose
    """
    def backgroundInsulinDose(self, weight):
        if weight > 130 or weight < 40:
            return None

        """
        The general approach is to take 0.55 multiplied by the weight in
        kilograms as the total (i.e., mealtime plus background) daily insulin
        requirement. The background insulin dose is generally 50%  of that total.
        """
        return (ratio * weight)/2

    """Determines an individual's sensitivity to one unit of insulin
    Keyword arguments:
    activity_level -- today’s physical activity level (between 0 and 10)
    k_activity -- K samples of physical activity level in some day (between 0 and 10)
    k_drops -- K  samples  of  drops  in  blood  sugar  from  one  unit  of  insulin  in  that  day  (between  15mg/dl and 100mg/dl)
    Returns: Background insulin dose
    """
    def personalSensitivityToInsulin(self, activity_level, k_activity, k_drops):
        if activity_level > 10 or activity_level < 0:
            return None

        if k_activity > 10 or k_activity < 0:
            return None

        if k_drops > 100 or k_drops < 15:
            return None


def main():
    weight = input("Weight")
    ic = InsulinDoseCalculator()
    print(ic.backgroundInsulinDose(weight))

if __name__ == '__main__':
    main()
